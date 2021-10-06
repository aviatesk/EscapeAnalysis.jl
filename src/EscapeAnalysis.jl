module EscapeAnalysis

let
    README = normpath(dirname(@__DIR__), "README.md")
    include_dependency(README)
    @doc read(README, String) EscapeAnalysis
end

export
    analyze_escapes,
    @analyze_escapes

import Core:
    CodeInfo,
    CodeInstance,
    MethodInstance,
    Const,
    Argument,
    SSAValue,
    PiNode,
    PhiNode,
    UpsilonNode,
    PhiCNode,
    ReturnNode,
    GotoNode,
    GotoIfNot,
    SimpleVector

const CC = Core.Compiler

import .CC:
    AbstractInterpreter,
    NativeInterpreter,
    WorldView,
    WorldRange,
    InferenceParams,
    OptimizationParams,
    get_world_counter,
    get_inference_cache,
    lock_mi_inference,
    unlock_mi_inference,
    add_remark!,
    may_optimize,
    may_compress,
    may_discard_trees,
    verbose_stmt_info,
    code_cache,
    get_inference_cache,
    OptimizationState,
    IRCode,
    optimize,
    widenconst,
    argextype,
    singleton_type,
    IR_FLAG_EFFECT_FREE,
    is_meta_expr_head

import Base.Meta:
    isexpr

import Base:
    destructure_callex

using InteractiveUtils

let __init_hooks__ = []
    global __init__() = foreach(f->f(), __init_hooks__)
    global register_init_hook!(@nospecialize(f)) = push!(__init_hooks__, f)
end

mutable struct EscapeAnalyzer{State} <: AbstractInterpreter
    native::NativeInterpreter
    ir::IRCode
    state::State
    linfo::MethodInstance
    EscapeAnalyzer(native::NativeInterpreter) = new{EscapeState}(native)
end

CC.InferenceParams(interp::EscapeAnalyzer)    = InferenceParams(interp.native)
CC.OptimizationParams(interp::EscapeAnalyzer) = OptimizationParams(interp.native)
CC.get_world_counter(interp::EscapeAnalyzer)  = get_world_counter(interp.native)

CC.lock_mi_inference(::EscapeAnalyzer,   ::MethodInstance) = nothing
CC.unlock_mi_inference(::EscapeAnalyzer, ::MethodInstance) = nothing

CC.add_remark!(interp::EscapeAnalyzer, sv, s) = add_remark!(interp.native, sv, s)

CC.may_optimize(interp::EscapeAnalyzer)      = may_optimize(interp.native)
CC.may_compress(interp::EscapeAnalyzer)      = may_compress(interp.native)
CC.may_discard_trees(interp::EscapeAnalyzer) = may_discard_trees(interp.native)
CC.verbose_stmt_info(interp::EscapeAnalyzer) = verbose_stmt_info(interp.native)

CC.get_inference_cache(interp::EscapeAnalyzer) = get_inference_cache(interp.native)

const GLOBAL_CODE_CACHE = IdDict{MethodInstance,CodeInstance}()
__clear_code_cache!() = empty!(GLOBAL_CODE_CACHE)

function CC.code_cache(interp::EscapeAnalyzer)
    worlds = WorldRange(get_world_counter(interp))
    return WorldView(GlobalCache(), worlds)
end

struct GlobalCache end

CC.haskey(wvc::WorldView{GlobalCache}, mi::MethodInstance) = haskey(GLOBAL_CODE_CACHE, mi)

CC.get(wvc::WorldView{GlobalCache}, mi::MethodInstance, default) = get(GLOBAL_CODE_CACHE, mi, default)

CC.getindex(wvc::WorldView{GlobalCache}, mi::MethodInstance) = getindex(GLOBAL_CODE_CACHE, mi)

function CC.setindex!(wvc::WorldView{GlobalCache}, ci::CodeInstance, mi::MethodInstance)
    GLOBAL_CODE_CACHE[mi] = ci
    add_callback!(mi) # register the callback on invalidation
    return nothing
end

function add_callback!(linfo)
    if !isdefined(linfo, :callbacks)
        linfo.callbacks = Any[invalidate_cache!]
    else
        if !any(@nospecialize(cb)->cb===invalidate_cache!, linfo.callbacks)
            push!(linfo.callbacks, invalidate_cache!)
        end
    end
    return nothing
end

function invalidate_cache!(replaced, max_world, depth = 0)
    delete!(GLOBAL_CODE_CACHE, replaced)

    if isdefined(replaced, :backedges)
        for mi in replaced.backedges
            mi = mi::MethodInstance
            if !haskey(GLOBAL_CODE_CACHE, mi)
                continue # otherwise fall into infinite loop
            end
            invalidate_cache!(mi, max_world, depth+1)
        end
    end
    return nothing
end

# analysis
# ========

"""
    x::EscapeLattice

A lattice for escape information, which holds the following properties:
- `x.Analyzed::Bool`: not formally part of the lattice, indicates this statement has not been analyzed at all
- `x.ReturnEscape::BitSet`: keeps SSA numbers of return statements where it can be returned to the caller
  * `isempty(x.ReturnEscape)` means it never escapes to the caller
  * otherwise it indicates it will escape to the caller via return (possibly as a field),
    where `0 ∈ x.ReturnEscape` has the special meaning that it's visible to the caller
    simply because it's passed as call argument
- `x.ThrownEscape::Bool`: indicates it may escape to somewhere through an exception (possibly as a field)
- `x.GlobalEscape::Bool`: indicates it may escape to a global space an exception (possibly as a field)
- `x.ArgEscape::Int` (not implemented yet): indicates it will escape to the caller through `setfield!` on argument(s)
  * `-1` : no escape
  * `0` : unknown or multiple
  * `n` : through argument N

These attributes can be combined to create a partial lattice that has a finite height, given
that input program has a finite number of statements, which is assured by Julia's semantics.

There are utility constructors to create common `EscapeLattice`s, e.g.,
- `NoEscape()`: the bottom element of this lattice, meaning it won't escape to anywhere
- `AllEscape()`: the topmost element of this lattice, meaning it will escape to everywhere

The escape analysis will transition these elements from the bottom to the top,
in the same direction as Julia's native type inference routine.
An abstract state will be initialized with the bottom(-like) elements:
- the call arguments are initialized as `ArgumentReturnEscape()`, because they're visible from a caller immediately
- the other states are initialized as `NotAnalyzed()`, which is a special lattice element that
  is slightly lower than `NoEscape`, but at the same time doesn't represent any meaning
  other than it's not analyzed yet (thus it's not formally part of the lattice).
"""
struct EscapeLattice
    Analyzed::Bool
    ReturnEscape::BitSet
    ThrownEscape::Bool
    GlobalEscape::Bool
    # TODO: ArgEscape::Int
end

function Base.:(==)(x::EscapeLattice, y::EscapeLattice)
    return x.Analyzed === y.Analyzed &&
           x.ReturnEscape == y.ReturnEscape &&
           x.ThrownEscape === y.ThrownEscape &&
           x.GlobalEscape === y.GlobalEscape
end

# lattice constructors
# precompute default values in order to eliminate computations at callsites
const NO_RETURN = BitSet()
const ARGUMENT_RETURN = BitSet(0)
NotAnalyzed() = EscapeLattice(false, NO_RETURN, false, false) # not formally part of the lattice
NoEscape() = EscapeLattice(true, NO_RETURN, false, false)
ReturnEscape(pcs::BitSet) = EscapeLattice(true, pcs, false, false)
ReturnEscape(pc::Int) = ReturnEscape(BitSet(pc))
ArgumentReturnEscape() = ReturnEscape(ARGUMENT_RETURN)
ThrownEscape() = EscapeLattice(true, NO_RETURN, true, false)
GlobalEscape() = EscapeLattice(true, NO_RETURN, false, true)
let
    all_return = BitSet(0:100_000)
    global AllReturnEscape() = ReturnEscape(all_return) # used for `show`
    global AllEscape() = EscapeLattice(true, all_return, true, true)
end

# Convenience names for some ⊑ queries
export
    has_not_analyzed,
    has_no_escape,
    has_return_escape,
    has_thrown_escape,
    has_global_escape,
    has_all_escape,
    can_elide_finalizer
has_not_analyzed(x::EscapeLattice) = x == NotAnalyzed()
has_no_escape(x::EscapeLattice) = x ⊑ NoEscape()
has_return_escape(x::EscapeLattice) = !isempty(x.ReturnEscape)
has_return_escape(x::EscapeLattice, pc::Int) = pc in x.ReturnEscape
has_thrown_escape(x::EscapeLattice) = x.ThrownEscape
has_global_escape(x::EscapeLattice) = x.GlobalEscape
has_all_escape(x::EscapeLattice) = AllEscape() == x

"""
    can_elide_finalizer(x::EscapeLattice, pc::Int) -> Bool

Queries the validity of the finalizer elision optimization at the `return` site of statement `pc`,
which inserts `finalize` call when the lifetime of interested object ends.
Note that we don't need to take `x.ThrownEscape` into account because it would have never
been thrown when the program execution reaches the `return` site.
"""
function can_elide_finalizer(x::EscapeLattice, pc::Int)
    x.GlobalEscape && return false
    0 in x.ReturnEscape && return false
    return pc ∉ x.ReturnEscape
end

function ⊑(x::EscapeLattice, y::EscapeLattice)
    if x.Analyzed ≤ y.Analyzed &&
       x.ReturnEscape ⊆ y.ReturnEscape &&
       x.ThrownEscape ≤ y.ThrownEscape &&
       x.GlobalEscape ≤ y.GlobalEscape
       return true
    end
    return false
end
⋤(x::EscapeLattice, y::EscapeLattice) = ⊑(x, y) && !⊑(y, x)

function ⊔(x::EscapeLattice, y::EscapeLattice)
    return EscapeLattice(
        x.Analyzed | y.Analyzed,
        x.ReturnEscape ∪ y.ReturnEscape,
        x.ThrownEscape | y.ThrownEscape,
        x.GlobalEscape | y.GlobalEscape,
        )
end

function ⊓(x::EscapeLattice, y::EscapeLattice)
    return EscapeLattice(
        x.Analyzed & y.Analyzed,
        x.ReturnEscape ∩ y.ReturnEscape,
        x.ThrownEscape & y.ThrownEscape,
        x.GlobalEscape & y.GlobalEscape,
        )
end

# TODO setup a more effient struct for cache
# which can discard escape information on SSS values and arguments that don't join dispatch signature

"""
    state::EscapeState

Extended lattice that maps arguments and SSA values to escape information represented as `EscapeLattice`:
- `state.arguments::Vector{EscapeLattice}`: escape information about "arguments" – note that
  "argument" can include both call arguments and slots appearing in analysis frame
- `ssavalues::Vector{EscapeLattice}`: escape information about each SSA value
"""
struct EscapeState
    arguments::Vector{EscapeLattice}
    ssavalues::Vector{EscapeLattice}
end
function EscapeState(nslots::Int, nargs::Int, nstmts::Int)
    arguments = EscapeLattice[
        1 ≤ i ≤ nargs ? ArgumentReturnEscape() : NotAnalyzed() for i in 1:nslots]
    ssavalues = EscapeLattice[NotAnalyzed() for _ in 1:nstmts]
    return EscapeState(arguments, ssavalues)
end

# we preserve `IRCode` as well just for debugging purpose
const GLOBAL_ESCAPE_CACHE = IdDict{MethodInstance,Tuple{EscapeState,IRCode}}()
__clear_escape_cache!() = empty!(GLOBAL_ESCAPE_CACHE)

const Change  = Pair{Union{Argument,SSAValue},EscapeLattice}
const Changes = Vector{Change}

"""
    find_escapes(ir::IRCode, nargs::Int) -> EscapeState

Escape analysis implementation is based on the data-flow algorithm described in the paper [^MM02].
The analysis works on the lattice of [`EscapeLattice`](@ref) and transitions lattice elements
from the bottom to the top in a _backward_ way, i.e. data flows from usage cites to definitions,
until every lattice gets converged to a fixed point by maintaining a (conceptual) working set
that contains program counters corresponding to remaining SSA statements to be analyzed.
Note that the analysis only manages a single global state, with some flow-sensitivity
encoded as property of `EscapeLattice`.

[^MM02]: A Graph-Free approach to Data-Flow Analysis.
         Markas Mohnen, 2002, April.
         <https://api.semanticscholar.org/CorpusID:28519618>
"""
function find_escapes(ir::IRCode, nargs::Int)
    (; stmts, sptypes, argtypes) = ir
    nstmts = length(stmts)

    # only manage a single state, some flow-sensitivity is encoded as `EscapeLattice` properties
    state = EscapeState(length(ir.argtypes), nargs, nstmts)
    changes = Changes() # stashes changes that happen at current statement

    while true
        local anyupdate = false

        for pc in nstmts:-1:1
            stmt = stmts.inst[pc]

            # we escape statements with the `ThrownEscape` property using the effect-freeness
            # information computed by the inliner
            is_effect_free = stmts.flag[pc] & IR_FLAG_EFFECT_FREE ≠ 0

            # collect escape information
            if isa(stmt, Expr)
                head = stmt.head
                if head === :call
                    has_changes = escape_call!(stmt.args, pc, state, ir, changes)
                    if !is_effect_free
                        add_changes!(stmt.args, ir, ThrownEscape(), changes)
                    else
                        has_changes || continue
                    end
                elseif head === :invoke
                    escape_invoke!(stmt.args, pc, state, ir, changes)
                elseif head === :new
                    info = state.ssavalues[pc]
                    if info == NotAnalyzed()
                        info = NoEscape()
                        add_change!(SSAValue(pc), ir, info, changes) # we will be interested in if this allocation escapes or not
                    end
                    add_changes!(stmt.args[2:end], ir, info, changes)
                elseif head === :splatnew
                    info = state.ssavalues[pc]
                    if info == NotAnalyzed()
                        info = NoEscape()
                        add_change!(SSAValue(pc), ir, info, changes) # we will be interested in if this allocation escapes or not
                    end
                    # splatnew passes field values using a single tuple (args[2])
                    add_change!(stmt.args[2], ir, info, changes)
                elseif head === :(=)
                    lhs, rhs = stmt.args
                    if isa(lhs, GlobalRef) # global store
                        add_change!(rhs, ir, GlobalEscape(), changes)
                    end
                elseif head === :foreigncall
                    # for foreigncall we simply escape every argument (args[6:length(args[3])])
                    # and its name (args[1])
                    # TODO: we can apply a similar strategy like builtin calls to specialize some foreigncalls
                    foreigncall_nargs = length((stmt.args[3])::SimpleVector)
                    name = stmt.args[1]
                    # if normalize(name) === :jl_gc_add_finalizer_th
                    #     continue # XXX assume this finalizer call is valid for finalizer elision
                    # end
                    add_change!(name, ir, ThrownEscape(), changes)
                    add_changes!(stmt.args[6:5+foreigncall_nargs], ir, ThrownEscape(), changes)
                elseif head === :throw_undef_if_not # XXX when is this expression inserted ?
                    add_change!(stmt.args[1], ir, ThrownEscape(), changes)
                elseif is_meta_expr_head(head)
                    # meta expressions doesn't account for any usages
                    continue
                elseif head === :static_parameter
                    # :static_parameter refers any of static parameters, but since they exist
                    # statically, we're really not interested in their escapes
                    continue
                elseif head === :copyast
                    # copyast simply copies a surface syntax AST, and should never use any of arguments or SSA values
                    continue
                elseif head === :undefcheck
                    # undefcheck is temporarily inserted by compiler
                    # it will be processd be later pass so it won't change any of escape states
                    continue
                elseif head === :the_exception
                    # we don't propagate escape information on exceptions via this expression, but rather
                    # use a dedicated lattice property `ThrownEscape`
                    continue
                elseif head === :isdefined
                    # just returns `Bool`, nothing accounts for any usages
                    continue
                elseif head === :enter || head === :leave || head === :pop_exception
                    # these exception frame managements doesn't account for any usages
                    # we can just ignore escape information from
                    continue
                elseif head === :gc_preserve_begin || head === :gc_preserve_end
                    # `GC.@preserve` may "use" arbitrary values, but we can just ignore the escape information
                    # imposed on `GC.@preserve` expressions since they're supposed to never be used elsewhere
                    continue
                else
                    add_changes!(stmt.args, ir, AllEscape(), changes)
                end
            elseif isa(stmt, GlobalRef) # global load
                add_change!(SSAValue(pc), ir, GlobalEscape(), changes)
            elseif isa(stmt, PiNode)
                if isdefined(stmt, :val)
                    info = state.ssavalues[pc]
                    add_change!(stmt.val, ir, info, changes)
                end
            elseif isa(stmt, PhiNode)
                info = state.ssavalues[pc]
                values = stmt.values
                for i in 1:length(values)
                    if isassigned(values, i)
                        add_change!(values[i], ir, info, changes)
                    end
                end
            elseif isa(stmt, PhiCNode)
                info = state.ssavalues[pc]
                values = stmt.values
                for i in 1:length(values)
                    if isassigned(values, i)
                        add_change!(values[i], ir, info, changes)
                    end
                end
            elseif isa(stmt, UpsilonNode)
                if isdefined(stmt, :val)
                    info = state.ssavalues[pc]
                    add_change!(stmt.val, ir, info, changes)
                end
            elseif isa(stmt, ReturnNode)
                if isdefined(stmt, :val)
                    add_change!(stmt.val, ir, ReturnEscape(pc), changes)
                end
            else
                @assert stmt isa GotoNode || stmt isa GotoIfNot || stmt isa GlobalRef || isnothing(stmt) # TODO remove me
                continue
            end

            isempty(changes) && continue

            anyupdate |= propagate_changes!(state, changes)

            empty!(changes)
        end

        anyupdate || break
    end

    return state
end

# propagate changes, and check convergence
function propagate_changes!(state::EscapeState, changes::Changes)
    local anychanged = false

    for (x, info) in changes
        if isa(x, Argument)
            old = state.arguments[x.n]
            new = old ⊔ info
            if old ≠ new
                state.arguments[x.n] = new
                anychanged |= true
            end
        elseif isa(x, SSAValue)
            old = state.ssavalues[x.id]
            new = old ⊔ info
            if old ≠ new
                state.ssavalues[x.id] = new
                anychanged |= true
            end
        end
    end

    return anychanged
end

# function normalize(@nospecialize(x))
#     if isa(x, QuoteNode)
#         return x.value
#     else
#         return x
#     end
# end

function add_changes!(args::Vector{Any}, ir::IRCode, info::EscapeLattice, changes::Changes)
    for x in args
        add_change!(x, ir, info, changes)
    end
end

function add_change!(@nospecialize(x), ir::IRCode, info::EscapeLattice, changes::Changes)
    if isa(x, Argument) || isa(x, SSAValue)
        if !isbitstype(widenconst(argextype(x, ir, ir.sptypes, ir.argtypes)))
            push!(changes, Change(x, info))
        end
    end
end

function escape_invoke!(args::Vector{Any}, pc::Int,
                        state::EscapeState, ir::IRCode, changes::Changes)
    linfo = first(args)::MethodInstance
    cache = get(GLOBAL_ESCAPE_CACHE, linfo, nothing)
    args = args[2:end]
    if isnothing(cache)
        add_changes!(args, ir, AllEscape(), changes)
    else
        (linfostate, _ #=ir::IRCode=#) = cache
        retinfo = state.ssavalues[pc] # escape information imposed on the call statement
        nargs = Int((linfo.def::Method).nargs)
        for i in 1:length(args)
            arg = args[i]
            if i ≤ nargs
                arginfo = linfostate.arguments[i]
            else # handle isva signature: COMBAK will this invalid once we encode alias information ?
                arginfo = linfostate.arguments[nargs]
            end
            if isempty(arginfo.ReturnEscape)
                @eval Main (ir = $ir; linfo = $linfo)
                error("invalid escape lattice element returned from inter-procedural context: inspect `Main.ir` and `Main.linfo`")
            end
            info = from_interprocedural(arginfo, retinfo)
            add_change!(arg, ir, info, changes)
        end
    end
end

# reinterpret the escape information imposed on the callee argument (`arginfo`) in the
# context of the caller frame using the escape information imposed on the return value (`retinfo`)
function from_interprocedural(arginfo::EscapeLattice, retinfo::EscapeLattice)
    ar = arginfo.ReturnEscape
    newarginfo = EscapeLattice(true, NO_RETURN, arginfo.ThrownEscape, arginfo.GlobalEscape)
    if ar == ARGUMENT_RETURN
        # if this is simply passed as the call argument, we can discard the `ReturnEscape`
        # information and just propagate the other escape information
        return newarginfo
    else
        # if this can be a return value, we have to merge it with the escape information
        return newarginfo ⊔ retinfo
    end
end

function escape_call!(args::Vector{Any}, pc::Int,
                      state::EscapeState, ir::IRCode, changes::Changes)
    ft = argextype(first(args), ir, ir.sptypes, ir.argtypes)
    f = singleton_type(ft)
    if isa(f, Core.IntrinsicFunction)
        return false # COMBAK we may break soundness here, e.g. `pointerref`
    end
    ishandled = escape_builtin!(f, args, pc, state, ir, changes)::Union{Nothing,Bool}
    isnothing(ishandled) && return false # nothing to propagate
    if !ishandled
        # if this call hasn't been handled by any of pre-defined handlers,
        # we escape this call conservatively
        add_changes!(args[2:end], ir, AllEscape(), changes)
    end
    return true
end

# TODO implement more builtins, make them more accurate
# TODO use `T_IFUNC`-like logic and don't not abuse dispatch ?

escape_builtin!(@nospecialize(f), _...) = return false

escape_builtin!(::typeof(isa), _...) = return nothing
escape_builtin!(::typeof(typeof), _...) = return nothing
escape_builtin!(::typeof(Core.sizeof), _...) = return nothing
escape_builtin!(::typeof(===), _...) = return nothing

function escape_builtin!(::typeof(ifelse), args::Vector{Any}, pc::Int, state::EscapeState, ir::IRCode, changes::Changes)
    length(args) == 4 || return false
    f, cond, th, el = args
    info = state.ssavalues[pc]
    condt = argextype(cond, ir, ir.sptypes, ir.argtypes)
    if isa(condt, Const) && (cond = condt.val; isa(cond, Bool))
        if cond
            add_change!(th, ir, info, changes)
        else
            add_change!(el, ir, info, changes)
        end
    else
        add_change!(th, ir, info, changes)
        add_change!(el, ir, info, changes)
    end
    return true
end

function escape_builtin!(::typeof(typeassert), args::Vector{Any}, pc::Int, state::EscapeState, ir::IRCode, changes::Changes)
    length(args) == 3 || return false
    f, obj, typ = args
    info = state.ssavalues[pc]
    add_change!(obj, ir, info, changes)
    return true
end

function escape_builtin!(::typeof(tuple), args::Vector{Any}, pc::Int, state::EscapeState, ir::IRCode, changes::Changes)
    info = state.ssavalues[pc]
    if info == NotAnalyzed()
        info = NoEscape()
    end
    add_changes!(args[2:end], ir, info, changes)
    return true
end

# TODO don't propagate escape information to the 1st argument, but propagate information to aliased field
function escape_builtin!(::typeof(getfield), args::Vector{Any}, pc::Int, state::EscapeState, ir::IRCode, changes::Changes)
    info = state.ssavalues[pc]
    if info == NotAnalyzed()
        info = NoEscape()
    end
    # only propagate info when the field itself is non-bitstype
    if !isbitstype(widenconst(ir.stmts.type[pc]))
        add_changes!(args[2:end], ir, info, changes)
    end
    return true
end

# entries
# =======

function CC.optimize(interp::EscapeAnalyzer, opt::OptimizationState, params::OptimizationParams, @nospecialize(result))
    ir = run_passes_with_escape_analysis(interp, opt.src, opt)
    return CC.finish(interp, opt, params, ir, result)
end

# TODO implement finalizer elision optimization
function elide_finalizers(ir::IRCode, state::EscapeState)
    return ir
end

# HACK enable copy and paste from Core.Compiler
function run_passes_with_escape_analysis end
register_init_hook!() do
@eval CC begin
    function $EscapeAnalysis.run_passes_with_escape_analysis(interp::$EscapeAnalyzer, ci::CodeInfo, sv::OptimizationState)
        preserve_coverage = coverage_enabled(sv.mod)
        ir = convert_to_ircode(ci, copy_exprargs(ci.code), preserve_coverage, sv)
        ir = slot2reg(ir, ci, sv)
        #@Base.show ("after_construct", ir)
        # TODO: Domsorting can produce an updated domtree - no need to recompute here
        @timeit "compact 1" ir = compact!(ir)
        @timeit "Inlining" ir = ssa_inlining_pass!(ir, ir.linetable, sv.inlining, ci.propagate_inbounds)
        #@timeit "verify 2" verify_ir(ir)
        ir = compact!(ir)
        svdef = sv.linfo.def
        nargs = isa(svdef, Method) ? Int(svdef.nargs) : 0
        @timeit "collect escape information" state = $find_escapes(ir, nargs)
        cacheir = copy(ir)
        # cache
        $setindex!($GLOBAL_ESCAPE_CACHE, (state, cacheir), sv.linfo)
        # for entry result
        interp.ir = cacheir
        interp.state = state
        interp.linfo = sv.linfo
        @timeit "finalizer elision" ir = $elide_finalizers(ir, state)
        #@Base.show ("before_sroa", ir)
        @timeit "SROA" ir = getfield_elim_pass!(ir)
        #@Base.show ir.new_nodes
        #@Base.show ("after_sroa", ir)
        ir = adce_pass!(ir)
        #@Base.show ("after_adce", ir)
        @timeit "type lift" ir = type_lift_pass!(ir)
        @timeit "compact 3" ir = compact!(ir)
        #@Base.show ir
        if JLOptions().debug_level == 2
            @timeit "verify 3" (verify_ir(ir); verify_linetable(ir.linetable))
        end
        return ir
    end
end
end # register_init_hook!() do

macro analyze_escapes(ex0...)
    return InteractiveUtils.gen_call_with_extracted_types_and_kwargs(__module__, :analyze_escapes, ex0)
end

function analyze_escapes(@nospecialize(f), @nospecialize(types=Tuple{});
                         world = get_world_counter(),
                         interp = Core.Compiler.NativeInterpreter(world))
    interp = EscapeAnalyzer(interp)
    results = code_typed(f, types; optimize=true, world, interp)
    isone(length(results)) || throw(ArgumentError("`analyze_escapes` only supports single analysis result"))
    return EscapeResult(interp.ir, interp.state, interp.linfo)
end

# utilities
# =========

# in order to run a whole analysis from ground zero (e.g. for benchmarking, etc.)
__clear_caches!() = (__clear_code_cache!(); __clear_escape_cache!())

function get_name_color(x::EscapeLattice, symbol::Bool = false)
    getname(x) = string(nameof(x))
    if x == NotAnalyzed()
        name, color = (getname(NotAnalyzed), '◌'), :plain
    elseif x == NoEscape()
        name, color = (getname(NoEscape), '✓'), :green
    elseif NoEscape() ⋤ x ⊑ AllReturnEscape()
        pcs = sprint(show, collect(x.ReturnEscape); context=:limit=>true)
        name1 = string(getname(ReturnEscape), '(', pcs, ')')
        name = name1, '↑'
        color = :cyan
    elseif NoEscape() ⋤ x ⊑ ThrownEscape()
        name, color = (getname(ThrownEscape), '↓'), :yellow
    elseif NoEscape() ⋤ x ⊑ GlobalEscape()
        name, color = (getname(GlobalEscape), 'G'), :red
    elseif x == AllEscape()
        name, color = (getname(AllEscape), '*'), :red
    else
        name, color = (nothing, '*'), :red
    end
    return (symbol ? last(name) : first(name), color)
end

function Base.show(io::IO, x::EscapeLattice)
    name, color = get_name_color(x)
    if isnothing(name)
        Base.@invoke show(io::IO, x::Any)
    else
        printstyled(io, name; color)
    end
end
function Base.show(io::IO, ::MIME"application/prs.juno.inline", x::EscapeLattice)
    name, color = get_name_color(x)
    if isnothing(name)
        return x # use fancy tree-view
    else
        printstyled(io, name; color)
    end
end

struct EscapeResult
    ir::IRCode
    state::EscapeState
    linfo::Union{Nothing,MethodInstance}
    EscapeResult(ir::IRCode, state::EscapeState, linfo::Union{Nothing,MethodInstance} = nothing) =
        new(ir, state, linfo)
end
Base.show(io::IO, result::EscapeResult) = print_with_info(io, result.ir, result.state, result.linfo)
@eval Base.iterate(res::EscapeResult, state=1) =
    return state > $(fieldcount(EscapeResult)) ? nothing : (getfield(res, state), state+1)

# adapted from https://github.com/JuliaDebug/LoweredCodeUtils.jl/blob/4612349432447e868cf9285f647108f43bd0a11c/src/codeedges.jl#L881-L897
function print_with_info(io::IO,
    ir::IRCode, (; arguments, ssavalues)::EscapeState, linfo::Union{Nothing,MethodInstance})
    # print escape information on SSA values
    function preprint(io::IO)
        ft = ir.argtypes[1]
        f = singleton_type(ft)
        if f === nothing
            f = widenconst(ft)
        end
        print(io, f, '(')
        for (i, arg) in enumerate(arguments)
            i == 1 && continue
            c, color = get_name_color(arg, true)
            printstyled(io, '_', i, "::", ir.argtypes[i], ' ', c; color)
            i ≠ length(arguments) && print(io, ", ")
        end
        print(io, ')')
        if !isnothing(linfo)
            def = linfo.def
            printstyled(io, " in ", (isa(def, Module) ? (def,) : (def.module, " at ", def.file, ':', def.line))...; color=:bold)
        end
        println(io)
    end

    # print escape information on SSA values
    # nd = ndigits(length(ssavalues))
    function preprint(io::IO, idx::Int)
        c, color = get_name_color(ssavalues[idx], true)
        # printstyled(io, lpad(idx, nd), ' ', c, ' '; color)
        printstyled(io, c, ' '; color)
    end

    print_with_info(preprint, (args...)->nothing, io, ir)
end

function print_with_info(preprint, postprint, io::IO, ir::IRCode)
    io = IOContext(io, :displaysize=>displaysize(io))
    used = Base.IRShow.stmts_used(io, ir)
    # line_info_preprinter = Base.IRShow.lineinfo_disabled
    line_info_preprinter = function (io::IO, indent::String, idx::Int)
        r = Base.IRShow.inline_linfo_printer(ir)(io, indent, idx)
        idx ≠ 0 && preprint(io, idx)
        return r
    end
    line_info_postprinter = Base.IRShow.default_expr_type_printer
    preprint(io)
    bb_idx_prev = bb_idx = 1
    for idx = 1:length(ir.stmts)
        preprint(io, idx)
        bb_idx = Base.IRShow.show_ir_stmt(io, ir, idx, line_info_preprinter, line_info_postprinter, used, ir.cfg, bb_idx)
        postprint(io, idx, bb_idx != bb_idx_prev)
        bb_idx_prev = bb_idx
    end
    max_bb_idx_size = ndigits(length(ir.cfg.blocks))
    line_info_preprinter(io, " "^(max_bb_idx_size + 2), 0)
    postprint(io)
    return nothing
end

end # module EscapeAnalysis

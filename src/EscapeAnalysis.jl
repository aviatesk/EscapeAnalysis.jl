module EscapeAnalysis

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
    argtype_to_function,
    IR_FLAG_EFFECT_FREE,
    is_meta_expr_head

import Base.Meta:
    isexpr

import Base:
    destructure_callex

using InteractiveUtils

let __init_hooks__ = []
    global __init__, register_init_hook!
    __init__() = foreach(f->f(), __init_hooks__)
    register_init_hook!(@nospecialize(f)) = push!(__init_hooks__, f)
end

mutable struct EscapeAnalyzer{Info} <: AbstractInterpreter
    native::NativeInterpreter
    source::Union{Nothing,IRCode}
    info::Union{Nothing,Info}
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
    abstract type EscapeLattice end

A lattice for escape information, which holds the following properties:
- `Analyzed`: not formally part of the lattice, indicates this statement has not been analyzed at all
- `ReturnEscape`: indicates it will escape to the caller via return (possibly as a field)
- `ArgEscape`: indicates it will escape to the caller through `setfield!` on argument(s)
  -1 : no escape
   0 : unknown or multiple
   n : through argument N

These attributes can be combined to create a partial lattice:
(note that this is inverted from the order used for the lattice in Core.Compiler)
- `NoEscape`: the topmost element of this lattice
- `Escape`: the inverse of NoEscape
- `AllEscape`: the bottom element of this lattice, meaning it will escape to everywhere

An abstract state will be initialized with the top(most) elements, and an escape analysis
will transition these elements from the top to the bottom.
"""
struct EscapeLattice
    Analyzed::Bool
    ReturnEscape::Bool
    OtherEscape::Bool
    # TODO: ArgEscape::Int
end

NoInformation() = EscapeLattice(false, false, false) # not formally part of the lattice
NoEscape() = EscapeLattice(true, false, false)
ReturnEscape() = EscapeLattice(true, true, false)
#=Other=#Escape() = EscapeLattice(true, false, true)
AllEscape() = EscapeLattice(true, true, true)

export is_no_escape, is_escape, is_return_escape
# Convenience names for some ⊑ queries
# TODO: these should be renamed to has_escape, has_return_escape, etc.
is_no_escape(x::EscapeLattice) = x === NoEscape()
is_escape(x::EscapeLattice) = !is_no_escape(x)
is_all_escape(x::EscapeLattice) = x === AllEscape()
is_return_escape(x::EscapeLattice) = x.ReturnEscape

function ⊑(x::EscapeLattice, y::EscapeLattice)
    if x.Analyzed <= y.Analyzed &&
       x.ReturnEscape <= y.ReturnEscape &&
       x.OtherEscape <= y.OtherEscape
       return true
    end
    return false
end

function ⊔(x::EscapeLattice, y::EscapeLattice)
    return EscapeLattice(
        x.Analyzed & y.Analyzed,
        x.ReturnEscape & y.ReturnEscape,
        x.OtherEscape & y.OtherEscape)
end

function ⊓(x::EscapeLattice, y::EscapeLattice)
    return EscapeLattice(
        x.Analyzed | y.Analyzed,
        x.ReturnEscape | y.ReturnEscape,
        x.OtherEscape | y.OtherEscape)
end

# extend lattices of escape information to lattices of mappings of arguments and SSA stmts to escape information
# ⊓ and ⊔ operate pair-wise, and from there we can just rely on the Base implementation for dictionary equality comparison
struct EscapeState
    arguments::Vector{EscapeLattice}
    ssavalues::Vector{EscapeLattice}
end
function EscapeState(nslots::Int, nargs::Int, nstmts::Int)
    arguments = EscapeLattice[
        i ≤ nargs ? ReturnEscape() : NoEscape() for i in 1:nslots]
    ssavalues = EscapeLattice[NoInformation() for _ in 1:nstmts]
    return EscapeState(arguments, ssavalues)
end
Base.copy(s::EscapeState) = EscapeState(copy(s.arguments), copy(s.ssavalues))

⊔(X::EscapeState, Y::EscapeState) = EscapeState(
    EscapeLattice[x ⊔ y for (x, y) in zip(X.arguments, Y.arguments)],
    EscapeLattice[x ⊔ y for (x, y) in zip(X.ssavalues, Y.ssavalues)])
⊓(X::EscapeState, Y::EscapeState) = EscapeState(
    EscapeLattice[x ⊓ y for (x, y) in zip(X.arguments, Y.arguments)],
    EscapeLattice[x ⊓ y for (x, y) in zip(X.ssavalues, Y.ssavalues)])
Base.:(==)(X::EscapeState, Y::EscapeState) = X.arguments == Y.arguments && X.ssavalues == Y.ssavalues

const GLOBAL_ESCAPE_CACHE = IdDict{MethodInstance,EscapeState}()
__clear_escape_cache!() = empty!(GLOBAL_ESCAPE_CACHE)

# An escape analysis implementation based on the algorithm described in the paper [MM02].
# The analysis works on the lattice of `EscapeLattice` and transitions lattice elements
# from the top to the bottom in a backward way, i.e. data flows from usage cites to definitions.
#
# [MM02] A Graph-Free approach to Data-Flow Analysis.
#        Markas Mohnen, 2002, April.
#        https://api.semanticscholar.org/CorpusID:28519618

const Changes = Vector{Tuple{Any,EscapeLattice}}

# TODO
# - implement more builtin handling
# - (related to above) do alias analysis to some extent
# - maybe flow-sensitivity (with sparse analysis state)
function find_escapes(ir::IRCode, nargs::Int)
    (; stmts, sptypes, argtypes) = ir
    nstmts = length(stmts)
    state = EscapeState(length(ir.argtypes), nargs, nstmts) # flow-insensitive, only manage a single state

    while true
        local anyupdate = false
        local changes = Changes()

        for pc in nstmts:-1:1
            stmt = stmts.inst[pc]

            # inliner already computed effect-freeness of this statement (whether it may throw or not)
            # and if it may throw, we conservatively escape all the arguments
            is_effect_free = stmts.flag[pc] & IR_FLAG_EFFECT_FREE ≠ 0

            # collect escape information
            if isa(stmt, Expr)
                head = stmt.head
                if head === :call # TODO implement more builtins, make them more accurate
                    if !is_effect_free
                        # TODO we can have a look at builtins.c and limit the escaped arguments if any of them are not captured in the thrown exception
                        add_changes!(stmt.args[2:end], ir, Escape(), changes)
                    else
                        escape_call!(stmt.args, pc, state, ir, changes) || continue
                    end
                elseif head === :invoke
                    linfo = first(stmt.args)
                    escapes_for_call = get(GLOBAL_ESCAPE_CACHE, linfo, nothing)
                    if isnothing(escapes_for_call)
                        add_changes!(stmt.args[3:end], ir, Escape(), changes)
                    else
                        for (arg, info) in zip(stmt.args[2:end], escapes_for_call.arguments)
                            if info === ReturnEscape()
                                info = NoEscape()
                            end
                            push!(changes, (arg, info))
                        end
                    end
                elseif head === :new
                    info = state.ssavalues[pc]
                    info === NoInformation() && (info = NoEscape())
                    for arg in stmt.args[2:end]
                        push!(changes, (arg, info))
                    end
                    push!(changes, (SSAValue(pc), info)) # we will be interested in if this allocation is not escape or not
                elseif head === :splatnew
                    info = state.ssavalues[pc]
                    info === NoInformation() && (info = NoEscape())
                    # splatnew passes field values using a single tuple (args[2])
                    push!(changes, (stmt.args[2], info))
                    push!(changes, (SSAValue(pc), info)) # we will be interested in if this allocation is not escape or not
                elseif head === :(=)
                    lhs, rhs = stmt.args
                    if isa(lhs, GlobalRef)
                        add_change!(rhs, ir, Escape(), changes)
                    end
                elseif head === :cfunction
                    # for :cfunction we conservatively escapes all its arguments
                    add_changes!(stmt.args, ir, Escape(), changes)
                elseif head === :foreigncall
                    # for foreigncall we simply escape every argument (args[6:length(args[3])])
                    # and its name (args[1])
                    # TODO: we can apply similar strategy like builtin calls
                    #       to specialize some foreigncalls
                    foreigncall_nargs = length((stmt.args[3])::SimpleVector)
                    push!(changes, (stmt.args[1], Escape()))
                    add_changes!(stmt.args[6:5+foreigncall_nargs], ir, Escape(), changes)
                elseif is_meta_expr_head(head)
                    continue
                elseif head === :static_parameter
                    # static_parameter reference static parameter using index
                    continue
                elseif head === :copyast
                    # copyast simply copies a surface syntax AST
                    continue
                elseif head === :undefcheck
                    # undefcheck is temporarily inserted by compiler
                    # it will be processd be later pass so it won't change any of escape states
                    continue
                elseif head === :throw_undef_if_not
                    # conservatively escapes the val argument (argument[1])
                    add_change!(stmt.args[1], ir, Escape(), changes)
                elseif head === :the_exception
                    continue
                elseif head === :isdefined
                    continue
                elseif head === :enter || head === :leave || head === :pop_exception
                    continue
                elseif head === :gc_preserve_begin || head === :gc_preserve_end
                    continue
                else # TODO: this is too conservative
                    add_changes!(stmt.args, ir, Escape(), changes)
                end
            elseif isa(stmt, PiNode)
                if isdefined(stmt, :val)
                    info = state.ssavalues[pc]
                    push!(changes, (stmt.val, info))
                end
            elseif isa(stmt, PhiNode)
                info = state.ssavalues[pc]
                values = stmt.values
                for i in 1:length(values)
                    if isassigned(values, i)
                        push!(changes, (values[i], info))
                    end
                end
            elseif isa(stmt, PhiCNode)
                info = state.ssavalues[pc]
                values = stmt.values
                for i in 1:length(values)
                    if isassigned(values, i)
                        push!(changes, (values[i], info))
                    end
                end
            elseif isa(stmt, UpsilonNode)
                if isdefined(stmt, :val)
                    info = state.ssavalues[pc]
                    push!(changes, (stmt.val, info))
                end
            elseif isa(stmt, ReturnNode)
                if isdefined(stmt, :val)
                    add_change!(stmt.val, ir, ReturnEscape(), changes)
                end
            else
                @assert stmt isa GotoNode || stmt isa GotoIfNot || stmt isa GlobalRef || isnothing(stmt) # TODO remove me
                continue
            end

            isempty(changes) && continue

            # propagate changes
            new = copy(state)
            for (x, info) in changes
                if isa(x, Argument)
                    new.arguments[x.n] = new.arguments[x.n] ⊓ info
                elseif isa(x, SSAValue)
                    new.ssavalues[x.id] = new.ssavalues[x.id] ⊓ info
                end
            end
            empty!(changes)

            # convergence check and worklist update
            if new ≠ state
                state = new

                anyupdate |= true
            end
        end

        anyupdate || break
    end

    return state
end

function add_changes!(args::Vector{Any}, ir::IRCode, info::EscapeLattice, changes::Changes)
    for x in args
        add_change!(x, ir, info, changes)
    end
end

function add_change!(@nospecialize(x), ir::IRCode, info::EscapeLattice, changes::Changes)
    if !isbitstype(widenconst(argextype(x, ir, ir.sptypes, ir.argtypes)))
        push!(changes, (x, info))
    end
end

function escape_call!(args::Vector{Any}, pc::Int, state::EscapeState, ir::IRCode, changes::Changes)
    ft = argextype(first(args), ir, ir.sptypes, ir.argtypes)
    f = argtype_to_function(ft)
    if isa(f, Core.IntrinsicFunction)
        ishandled = nothing # XXX we may break soundness here, e.g. `pointerref`
    else
        ishandled = escape_builtin!(f, args, pc, state, ir, changes)::Union{Nothing,Bool}
    end
    isnothing(ishandled) && return false # nothing to propagate
    if !ishandled
        # if this call hasn't been handled by any of pre-defined handlers,
        # we escape this call conservatively
        add_changes!(args[2:end], ir, Escape(), changes)
    end
    return true
end

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
    if isa(condt, Const) && isa(condt.val, Bool)
        if condt.val
            push!(changes, (th, info))
        else
            push!(changes, (el, info))
        end
    else
        push!(changes, (th, info))
        push!(changes, (el, info))
    end
    return true
end

function escape_builtin!(::typeof(tuple), args::Vector{Any}, pc::Int, state::EscapeState, ir::IRCode, changes::Changes)
    info = state.ssavalues[pc]
    info === NoInformation() && (info = NoEscape())
    # TODO: we may want to remove this check when we implement the alias analysis
    add_changes!(args[2:end], ir, info, changes)
    return true
end

# TODO don't propagate escape information to the 1st argument, but propagate information to aliased field
function escape_builtin!(::typeof(getfield), args::Vector{Any}, pc::Int, state::EscapeState, ir::IRCode, changes::Changes)
    info = state.ssavalues[pc]
    info === NoInformation() && (info = NoEscape())
    rt = widenconst(ir.stmts.type[pc])
    # Only propagate info when the field itself is non-bitstype
    # TODO: we may want to remove this check when we implement the alias analysis
    if !isbitstype(rt)
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
        @timeit "collect escape information" escapes = $find_escapes(ir, nargs+1)
        $setindex!($GLOBAL_ESCAPE_CACHE, escapes, sv.linfo)
        interp.source = copy(ir)
        interp.info = escapes
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
    interp = EscapeAnalyzer{EscapeState}(interp, nothing, nothing)

    code_typed(f, types; optimize=true, world, interp)
    return EscapeAnalysisResult(interp.source, interp.info)
end

# utilities
# =========

# in order to run a whole analysis from ground zero (e.g. for benchmarking, etc.)
__clear_caches!() = (__clear_code_cache!(); __clear_escape_cache!())

struct EscapeAnalysisResult
    ir::IRCode
    state::EscapeState
end
Base.show(io::IO, result::EscapeAnalysisResult) = print_with_info(io, result.ir, result.state)

function Base.iterate(result::EscapeAnalysisResult, state = nothing)
    state == 2 && return nothing
    isnothing(state) && return result.ir, 1
    return result.state, 2
end

# adapted from https://github.com/JuliaDebug/LoweredCodeUtils.jl/blob/4612349432447e868cf9285f647108f43bd0a11c/src/codeedges.jl#L881-L897
function print_with_info(io::IO, ir::IRCode, (; arguments, ssavalues)::EscapeState)
    function char_color(info::EscapeLattice)
        return info === NoInformation() ? ('◌', :plain) :
               info === NoEscape() ? ('↓', :green) :
               info === ReturnEscape() ? ('↑', :yellow) :
               info === Escape() ? ('→', :red) :
               ('*', :red)
    end

    # print escape information on SSA values
    function preprint(io::IO)
        print(io, widenconst(ir.argtypes[1]), '(')
        for (i, arg) in enumerate(arguments)
            i == 1 && continue
            c, color = char_color(arg)
            printstyled(io, '_', i, "::", ir.argtypes[i], ' ', c; color)
            i ≠ length(arguments) && print(io, ", ")
        end
        println(io, ')')
    end

    # print escape information on SSA values
    nd = ndigits(length(ssavalues))
    function preprint(io::IO, idx::Int)
        c, color = char_color(ssavalues[idx])
        printstyled(io, lpad(idx, nd), ' ', c, ' '; color)
    end
    print_with_info(preprint, (args...)->nothing, io, ir)
end

function print_with_info(preprint, postprint, io::IO, ir::IRCode)
    io = IOContext(io, :displaysize=>displaysize(io))
    used = BitSet()
    used = Base.IRShow.stmts_used(io, ir)
    line_info_preprinter = Base.IRShow.lineinfo_disabled
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

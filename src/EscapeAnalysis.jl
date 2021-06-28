module EscapeAnalysis

import Core:
    CodeInfo,
    CodeInstance,
    MethodInstance,
    Argument,
    SSAValue,
    PiNode,
    PhiNode,
    UpsilonNode,
    PhiCNode,
    ReturnNode

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
    argextype

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

# CC.code_cache(interp::EscapeAnalyzer) = code_cache(interp.native)

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
    abstract type EscapeInformation end

A lattice for escape information, which has the following elements:
- `NoInformation`: the top element of this lattice, meaning no information is derived
- `NoEscape`: the second topmost element of this lattice, meaning it will not escape from this local frame
- `ReturnEscape`: a lattice that is lower than `NoEscape`, meaning it will escape to the caller
- `Escape`: the bottom element of this lattice, meaning it will escape to somewhere

An abstract state will be initialized with the top(most) elements, and an escape analysis
will transition these elements from the top to the bottom.
"""
abstract type EscapeInformation end

struct NoInformation <: EscapeInformation end
struct Escape        <: EscapeInformation end
struct NoEscape      <: EscapeInformation end
struct ReturnEscape  <: EscapeInformation end

⊑(x::EscapeInformation, y::EscapeInformation) = x == y
⊑(::Escape,             ::EscapeInformation)  = true
⊑(::EscapeInformation,  ::NoInformation)      = true
⊑(::Escape,             ::NoInformation)      = true # avoid ambiguity
⊑(::ReturnEscape,       ::NoEscape)           = true

⊔(x::EscapeInformation, y::EscapeInformation) = x⊑y ? y : y⊑x ? x : NoInformation()
⊓(x::EscapeInformation, y::EscapeInformation) = x⊑y ? x : y⊑x ? y : Escape()

# extend lattices of escape information to lattices of mappings of arguments and SSA stmts to escape information
# ⊓ and ⊔ operate pair-wise, and from there we can just rely on the Base implementation for dictionary equality comparison
struct EscapeState
    arguments::Vector{EscapeInformation}
    ssavalues::Vector{EscapeInformation}
end
function EscapeState(narguments::Int, nssavalues::Int)
    arguments = EscapeInformation[NoEscape() for _ in 1:narguments]
    ssavalues = EscapeInformation[NoInformation() for _ in 1:nssavalues]
    return EscapeState(arguments, ssavalues)
end
Base.copy(s::EscapeState) = EscapeState(copy(s.arguments), copy(s.ssavalues))

⊔(X::EscapeState, Y::EscapeState) = EscapeState(
    EscapeInformation[x ⊔ y for (x, y) in zip(X.arguments, Y.arguments)],
    EscapeInformation[x ⊔ y for (x, y) in zip(X.ssavalues, Y.ssavalues)])
⊓(X::EscapeState, Y::EscapeState) = EscapeState(
    EscapeInformation[x ⊓ y for (x, y) in zip(X.arguments, Y.arguments)],
    EscapeInformation[x ⊓ y for (x, y) in zip(X.ssavalues, Y.ssavalues)])
Base.:(==)(X::EscapeState, Y::EscapeState) = X.arguments == Y.arguments && X.ssavalues == Y.ssavalues

const GLOBAL_ESCAPE_CACHE = IdDict{MethodInstance,EscapeState}()
__clear_escape_cache!() = empty!(GLOBAL_ESCAPE_CACHE)

# An escape analysis implementation based on the algorithm described in the paper [MM02].
# The analysis works on the lattice of `EscapeInformation` and transitions lattice elements
# from the top to the bottom in a backward way, i.e. data flows from usage cites to definitions.
#
# [MM02] A Graph-Free approach to Data-Flow Analysis.
#        Markas Mohnen, 2002, April.
#        https://api.semanticscholar.org/CorpusID:28519618

# TODO
# - implement more builtin handling
# - (related to above) do alias analysis to some extent
# - maybe flow-sensitivity (with sparse analysis state)
function find_escapes(ir::IRCode)
    (; cfg, stmts) = ir
    n = length(stmts)
    state = EscapeState(length(ir.argtypes), n) # flow-insensitive, only manage a single state

    W = collect(n:-1:1) # worklist

    for pc in W
        stmt = stmts.inst[pc]

        changes = Pair{Any,EscapeInformation}[]

        # collect escape information
        if isa(stmt, Expr)
            head = stmt.head
            if head === :call
                ft = widenconst(argextype(first(stmt.args), ir, ir.sptypes, ir.argtypes))
                # TODO implement more builtins
                if ft <: Core.IntrinsicFunction
                elseif ft === typeof(isa) || ft === typeof(typeof)
                elseif ft === typeof(getfield) || ft === typeof(tuple)
                    info = state.ssavalues[pc]
                    info === NoInformation() && (info = NoEscape())
                    for arg in stmt.args[2:end]
                        push!(changes, arg => info)
                    end
                else
                    for arg in stmt.args[2:end]
                        push!(changes, arg => Escape())
                    end
                end
            elseif head === :invoke
                linfo = first(stmt.args)
                escapes_for_call = get(GLOBAL_ESCAPE_CACHE, linfo, nothing)
                if isnothing(escapes_for_call)
                    for arg in stmt.args[3:end]
                        push!(changes, arg => Escape())
                    end
                else
                    # @assert length(escapes_for_call.arguments) == linfo.def.nargs
                    for (arg, info) in zip(stmt.args[2:end], escapes_for_call.arguments)
                        push!(changes, arg => info)
                    end
                end
            elseif head === :new
                info = state.ssavalues[pc]
                info === NoInformation() && (info = NoEscape())
                for arg in stmt.args[2:end]
                    push!(changes, arg => info)
                end
            elseif head === :(=)
                lhs, rhs = stmt.args
                if isa(lhs, GlobalRef)
                    push!(changes, rhs => Escape())
                end
            elseif head === :enter || head === :leave || head === :pop_exception
            else # TODO: this is too conservative
                for arg in stmt.args
                    push!(changes, arg => Escape())
                end
            end
        elseif isa(stmt, PiNode)
            if isdefined(stmt, :val)
                info = state.ssavalues[pc]
                push!(changes, stmt.val => info)
            end
        elseif isa(stmt, PhiNode)
            info = state.ssavalues[pc]
            values = stmt.values
            for i in 1:length(values)
                if isassigned(values, i)
                    push!(changes, values[i] => info)
                end
            end
        elseif isa(stmt, PhiCNode)
            info = state.ssavalues[pc]
            values = stmt.values
            for i in 1:length(values)
                if isassigned(values, i)
                    push!(changes, values[i] => info)
                end
            end
        elseif isa(stmt, UpsilonNode)
            if isdefined(stmt, :val)
                info = state.ssavalues[pc]
                push!(changes, stmt.val => info)
            end
        elseif isa(stmt, ReturnNode)
            if isdefined(stmt, :val)
                push!(changes, stmt.val => ReturnEscape())
            end
        end

        # propagate changes
        new = copy(state)
        for (x, info) in changes
            if isa(x, Argument)
                new.arguments[x.n] = info
            elseif isa(x, SSAValue)
                new.ssavalues[x.id] = info
            end
        end

        # convergence check and worklist update
        if new != state
            state = new ⊓ state

            i = findfirst(==(pc), cfg.index)
            if !isnothing(i)
                block = cfg.blocks[i+1]
                for pred in block.preds
                    push!(W, last(cfg.blocks[pred].stmts))
                end
            elseif pc ≠ 1
                push!(W, pc-1)
            end
        end
    end

    return state
end

# entries
# =======

function CC.optimize(interp::EscapeAnalyzer, opt::OptimizationState, params::OptimizationParams, @nospecialize(result))
    nargs = Int(opt.nargs) - 1
    ir = run_passes_with_escape_analysis(interp, opt.src, nargs, opt)
    return CC.finish(interp, opt, params, ir, result)
end

# HACK enable copy and paste from Core.Compiler
function run_passes_with_escape_analysis end
register_init_hook!() do
@eval CC begin
    function $(EscapeAnalysis).run_passes_with_escape_analysis(interp::$EscapeAnalyzer, ci::CodeInfo, nargs::Int, sv::OptimizationState)
        preserve_coverage = coverage_enabled(sv.mod)
        ir = convert_to_ircode(ci, copy_exprargs(ci.code), preserve_coverage, nargs, sv)
        ir = slot2reg(ir, ci, nargs, sv)
        #@Base.show ("after_construct", ir)
        # TODO: Domsorting can produce an updated domtree - no need to recompute here
        @timeit "compact 1" ir = compact!(ir)
        @timeit "Inlining" ir = ssa_inlining_pass!(ir, ir.linetable, sv.inlining, ci.propagate_inbounds)
        #@timeit "verify 2" verify_ir(ir)
        ir = compact!(ir)
        @timeit "collect escape information" escapes = $find_escapes(ir)
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
    return interp.source, interp.info
end

export
    analyze_escapes,
    @analyze_escapes

end # module EscapeAnalysis

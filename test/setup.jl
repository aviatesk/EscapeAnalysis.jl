using EscapeAnalysis, Test, JET
import Core: Argument, SSAValue

@static if isdefined(Core.Compiler, :alloc_array_ndims)
    import Core.Compiler: alloc_array_ndims
else
    function alloc_array_ndims(name::Symbol)
        if name === :jl_alloc_array_1d
            return 1
        elseif name === :jl_alloc_array_2d
            return 2
        elseif name === :jl_alloc_array_3d
            return 3
        elseif name === :jl_new_array
            return 0
        end
        return nothing
    end
end

isT(T) = (@nospecialize x) -> x === T
issubT(T) = (@nospecialize x) -> x <: T
isreturn(@nospecialize x) = isa(x, Core.ReturnNode) && isdefined(x, :val)
isthrow(@nospecialize x) = Meta.isexpr(x, :call) && Core.Compiler.is_throw_call(x)
isnew(@nospecialize x) = Meta.isexpr(x, :new)
isϕ(@nospecialize x) = isa(x, Core.PhiNode)
function isarrayalloc(@nospecialize x)
    if Meta.isexpr(x, :foreigncall)
        name = x.args[1]
        nn = EscapeAnalysis.normalize(name)
        return alloc_array_ndims(nn) !== nothing
    end
    return false
end
import Core.Compiler: argextype, singleton_type
const EMPTY_SPTYPES = Any[]
iscall(y) = @nospecialize(x) -> iscall(y, x)
function iscall((ir, f), @nospecialize(x))
    return iscall(x) do @nospecialize x
        Core.Compiler.singleton_type(Core.Compiler.argextype(x, ir, EMPTY_SPTYPES)) === f
    end
end
iscall(pred::Function, @nospecialize(x)) = Meta.isexpr(x, :call) && pred(x.args[1])

let setup_ex = quote
        mutable struct SafeRef{T}
            x::T
        end
        Base.getindex(s::SafeRef) = getfield(s, 1)
        Base.setindex!(s::SafeRef, x) = setfield!(s, 1, x)

        mutable struct SafeRefs{S,T}
            x1::S
            x2::T
        end
        Base.getindex(s::SafeRefs, idx::Int) = getfield(s, idx)
        Base.setindex!(s::SafeRefs, x, idx::Int) = setfield!(s, idx, x)
    end
    global function EATModule(setup_ex = setup_ex)
        M = Module()
        Core.eval(M, setup_ex)
        return M
    end
    Core.eval(@__MODULE__, setup_ex)
end

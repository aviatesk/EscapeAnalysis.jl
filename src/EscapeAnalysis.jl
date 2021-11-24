baremodule EscapeAnalysis

export
    find_escapes,
    has_not_analyzed,
    has_no_escape,
    has_return_escape,
    has_thrown_escape,
    has_all_escape,
    can_elide_finalizer

# analysis
# ========

const _TOP_MOD = ccall(:jl_base_relative_to, Any, (Any,), EscapeAnalysis)::Module

# imports
import ._TOP_MOD: ==
# usings
import Core:
    MethodInstance, Const, Argument, SSAValue, PiNode, PhiNode, UpsilonNode, PhiCNode,
    ReturnNode, GotoNode, GotoIfNot, SimpleVector
import ._TOP_MOD:     # Base definitions
    @__MODULE__, @eval, @assert, @nospecialize, @inbounds, @inline, @noinline, @label, @goto,
    Vector, BitSet, IdDict, IdSet,
    !, !==, !=, ≠, +, -, ≤, <, ≥, >, &, |, include, error, missing, println,
    ∪, ⊆, ∩, :, length, get, first, last, in, isempty, isassigned, push!, empty!,
    max, min
import Core.Compiler: # Core.Compiler specific definitions
    IRCode, IR_FLAG_EFFECT_FREE,
    isbitstype, isexpr, is_meta_expr_head, widenconst, argextype, singleton_type,
    fieldcount_noerror, try_compute_fieldidx

if isdefined(Core.Compiler, :try_compute_field)
    import Core.Compiler: try_compute_field
else
    function try_compute_field(ir::IRCode, @nospecialize(field))
        # fields are usually literals, handle them manually
        if isa(field, QuoteNode)
            field = field.value
        elseif isa(field, Int) || isa(field, Symbol)
        # try to resolve other constants, e.g. global reference
        else
            field = argextype(field, ir)
            if isa(field, Const)
                field = field.val
            else
                return nothing
            end
        end
        return isa(field, Union{Int, Symbol}) ? field : nothing
    end
end

begin # A disjoint set implementation adapted from
      # https://github.com/JuliaCollections/DataStructures.jl/blob/f57330a3b46f779b261e6c07f199c88936f28839/src/disjoint_set.jl
      # under the MIT license: https://github.com/JuliaCollections/DataStructures.jl/blob/master/License.md

    # imports
    import ._TOP_MOD:
        length,
        eltype,
        union!,
        push!
    # usings
    import ._TOP_MOD:
        OneTo, collect, zero, zeros, one, typemax

    # Disjoint-Set

    ############################################################
    #
    #   A forest of disjoint sets of integers
    #
    #   Since each element is an integer, we can use arrays
    #   instead of dictionary (for efficiency)
    #
    #   Disjoint sets over other key types can be implemented
    #   based on an IntDisjointSet through a map from the key
    #   to an integer index
    #
    ############################################################

    _intdisjointset_bounds_err_msg(T) = "the maximum number of elements in IntDisjointSet{$T} is $(typemax(T))"

    """
        IntDisjointSet{T<:Integer}(n::Integer)

    A forest of disjoint sets of integers, which is a data structure
    (also called a union–find data structure or merge–find set)
    that tracks a set of elements partitioned
    into a number of disjoint (non-overlapping) subsets.
    """
    mutable struct IntDisjointSet{T<:Integer}
        parents::Vector{T}
        ranks::Vector{T}
        ngroups::T
    end

    IntDisjointSet(n::T) where {T<:Integer} = IntDisjointSet{T}(collect(OneTo(n)), zeros(T, n), n)
    IntDisjointSet{T}(n::Integer) where {T<:Integer} = IntDisjointSet{T}(collect(OneTo(T(n))), zeros(T, T(n)), T(n))
    length(s::IntDisjointSet) = length(s.parents)

    """
        num_groups(s::IntDisjointSet)

    Get a number of groups.
    """
    num_groups(s::IntDisjointSet) = s.ngroups
    eltype(::Type{IntDisjointSet{T}}) where {T<:Integer} = T

    # find the root element of the subset that contains x
    # path compression is implemented here
    function find_root_impl!(parents::Vector{T}, x::Integer) where {T<:Integer}
        p = parents[x]
        @inbounds if parents[p] != p
            parents[x] = p = _find_root_impl!(parents, p)
        end
        return p
    end

    # unsafe version of the above
    function _find_root_impl!(parents::Vector{T}, x::Integer) where {T<:Integer}
        @inbounds p = parents[x]
        @inbounds if parents[p] != p
            parents[x] = p = _find_root_impl!(parents, p)
        end
        return p
    end

    """
        find_root!(s::IntDisjointSet{T}, x::T)

    Find the root element of the subset that contains an member `x`.
    Path compression happens here.
    """
    find_root!(s::IntDisjointSet{T}, x::T) where {T<:Integer} = find_root_impl!(s.parents, x)

    """
        in_same_set(s::IntDisjointSet{T}, x::T, y::T)

    Returns `true` if `x` and `y` belong to the same subset in `s`, and `false` otherwise.
    """
    in_same_set(s::IntDisjointSet{T}, x::T, y::T) where {T<:Integer} = find_root!(s, x) == find_root!(s, y)

    """
        union!(s::IntDisjointSet{T}, x::T, y::T)

    Merge the subset containing `x` and that containing `y` into one
    and return the root of the new set.
    """
    function union!(s::IntDisjointSet{T}, x::T, y::T) where {T<:Integer}
        parents = s.parents
        xroot = find_root_impl!(parents, x)
        yroot = find_root_impl!(parents, y)
        return xroot != yroot ? root_union!(s, xroot, yroot) : xroot
    end

    """
        root_union!(s::IntDisjointSet{T}, x::T, y::T)

    Form a new set that is the union of the two sets whose root elements are
    `x` and `y` and return the root of the new set.
    Assume `x ≠ y` (unsafe).
    """
    function root_union!(s::IntDisjointSet{T}, x::T, y::T) where {T<:Integer}
        parents = s.parents
        rks = s.ranks
        @inbounds xrank = rks[x]
        @inbounds yrank = rks[y]

        if xrank < yrank
            x, y = y, x
        elseif xrank == yrank
            rks[x] += one(T)
        end
        @inbounds parents[y] = x
        s.ngroups -= one(T)
        return x
    end

    """
        push!(s::IntDisjointSet{T})

    Make a new subset with an automatically chosen new element `x`.
    Returns the new element. Throw an `ArgumentError` if the
    capacity of the set would be exceeded.
    """
    function push!(s::IntDisjointSet{T}) where {T<:Integer}
        l = length(s)
        l < typemax(T) || throw(ArgumentError(_intdisjointset_bounds_err_msg(T)))
        x = l + one(T)
        push!(s.parents, x)
        push!(s.ranks, zero(T))
        s.ngroups += one(T)
        return x
    end
end # begin

const FieldInfo  = IdSet{Any}
const FieldsInfo = Vector{FieldInfo}
struct UnintializedField end

"""
    x::EscapeLattice

A lattice for escape information, which holds the following properties:
- `x.Analyzed::Bool`: not formally part of the lattice, indicates `x` has not been analyzed at all
- `x.ReturnEscape::Bool`: indicates `x` may escape to the caller via return (possibly as a field),
    where `x.ReturnEscape && 0 ∈ x.EscapeSites` has the special meaning that it's visible to
    the caller simply because it's passed as call argument
- `x.ThrownEscape::Bool`: indicates `x` may escape to somewhere through an exception (possibly as a field)
- `x.EscapeSites::BitSet`: records program counters (SSA numbers) where `x` can escape
- `x.FieldSets::Union{Vector{IdSet{Any}},Bool}`: maintains the sets of possible values of fields of `x`:
  * `x.FieldSets === false` indicates the fields of `x` isn't analyzed yet
  * `x.FieldSets === true` indicates the fields of `x` can't be analyzed, e.g. the type of `x`
    is not concrete and thus the number of its fields can't known precisely
  * otherwise `x.FieldSets::Vector{IdSet{Any}}` holds all the possible values of each field,
    where `x.FieldSets[i]` keeps all possibilities that the `i`th field can be
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
    ReturnEscape::Bool
    ThrownEscape::Bool
    EscapeSites::BitSet
    FieldSets::Union{FieldsInfo,Bool}
    # TODO: ArgEscape::Int

    function EscapeLattice(Analyzed::Bool,
                           ReturnEscape::Bool,
                           ThrownEscape::Bool,
                           EscapeSites::BitSet,
                           FieldSets,
                           )
        @nospecialize FieldSets
        return new(
            Analyzed,
            ReturnEscape,
            ThrownEscape,
            EscapeSites,
            FieldSets,
            )
    end
    function EscapeLattice(x::EscapeLattice,
                           # non-concrete fields should be passed as default arguments
                           # in order to avoid allocating non-concrete `NamedTuple`s
                           FieldSets = x.FieldSets;
                           Analyzed::Bool = x.Analyzed,
                           ReturnEscape::Bool = x.ReturnEscape,
                           ThrownEscape::Bool = x.ThrownEscape,
                           EscapeSites::BitSet = x.EscapeSites,
                           )
        @nospecialize FieldSets
        return new(
            Analyzed,
            ReturnEscape,
            ThrownEscape,
            EscapeSites,
            FieldSets,
            )
    end
end

# precomputed default values in order to eliminate computations at each callsite
const EMPTY_ESCAPE_SITES = BitSet()
const ARGUMENT_ESCAPE_SITES = BitSet(0)

# the constructors
NotAnalyzed() = EscapeLattice(false, false, false, EMPTY_ESCAPE_SITES, false) # not formally part of the lattice
NoEscape() = EscapeLattice(true, false, false, EMPTY_ESCAPE_SITES, false)
ReturnEscape(pc::Int) = EscapeLattice(true, true, false, BitSet(pc), false)
ThrownEscape(pc::Int) = EscapeLattice(true, false, true, BitSet(pc), false)
ArgumentReturnEscape() = EscapeLattice(true, true, false, ARGUMENT_ESCAPE_SITES, true)
let
    ALL_ESCAPE_SITES = BitSet(0:100_000)
    global AllEscape() = EscapeLattice(true, true, true, ALL_ESCAPE_SITES, true)
    # used for `show`
    global AllReturnEscape() = EscapeLattice(true, true, false, ALL_ESCAPE_SITES, false)
    global AllThrownEscape() = EscapeLattice(true, false, true, ALL_ESCAPE_SITES, false)
end
ignore_fieldsets(info::EscapeLattice) =
    EscapeLattice(info, info.FieldSets === true ? true : false)

# Convenience names for some ⊑ queries
has_not_analyzed(x::EscapeLattice) = x == NotAnalyzed()
has_no_escape(x::EscapeLattice) = x ⊑ₑ NoEscape()
has_return_escape(x::EscapeLattice) = x.ReturnEscape
has_return_escape(x::EscapeLattice, pc::Int) = has_return_escape(x) && pc in x.EscapeSites
has_thrown_escape(x::EscapeLattice) = x.ThrownEscape
has_thrown_escape(x::EscapeLattice, pc::Int) = has_thrown_escape(x) && pc in x.EscapeSites
has_all_escape(x::EscapeLattice) = AllEscape() ⊑ x

"""
    can_elide_finalizer(x::EscapeLattice, pc::Int) -> Bool

Queries the validity of the finalizer elision optimization at the `return` site of statement `pc`,
which inserts `finalize` call when the lifetime of interested object ends.
Note that we don't need to take `x.ThrownEscape` into account because it would have never
been thrown when the program execution reaches the `return` site.
"""
can_elide_finalizer(x::EscapeLattice, pc::Int) =
    !(has_return_escape(x, 0) || has_return_escape(x, pc))

# we need to make sure this `==` operator corresponds to lattice equality rather than object equality,
# otherwise `propagate_changes` can't detect the convergence
x::EscapeLattice == y::EscapeLattice = begin
    xf, yf = x.FieldSets, y.FieldSets
    if isa(xf, Bool)
        isa(yf, Bool) || return false
        xf === yf || return false
    else
        isa(yf, Bool) && return false
        xf == yf || return false
    end
    return x.Analyzed === y.Analyzed &&
           x.ReturnEscape === y.ReturnEscape &&
           x.ThrownEscape === y.ThrownEscape &&
           x.EscapeSites == y.EscapeSites &&
           true
end

x::EscapeLattice ⊑ y::EscapeLattice = begin
    xf, yf = x.FieldSets, y.FieldSets
    if isa(xf, Bool)
        xf && yf !== true && return false
    else
        if isa(yf, Bool)
            yf === false && return false
        else
            xf, yf = xf::FieldsInfo, yf::FieldsInfo
            xn, yn = length(xf), length(yf)
            xn > yn && return false
            for i in 1:xn
                xf[i] ⊆ yf[i] || return false
            end
        end
    end
    return x ⊑ₑ y
end
x::EscapeLattice ⊑ₑ y::EscapeLattice = begin # partial order excluding the `FieldSets` order
    if x.Analyzed ≤ y.Analyzed &&
       x.ReturnEscape ≤ y.ReturnEscape &&
       x.ThrownEscape ≤ y.ThrownEscape &&
       x.EscapeSites ⊆ y.EscapeSites &&
       true
        return true
    end
    return false
end
x::EscapeLattice ⊏ y::EscapeLattice = x ⊑ y && !(y ⊑ x)
x::EscapeLattice ⊏ₑ y::EscapeLattice = x ⊑ₑ y && !(y ⊑ₑ x)
x::EscapeLattice ⋤ y::EscapeLattice = !(y ⊑ x)
x::EscapeLattice ⋤ₑ y::EscapeLattice = !(y ⊑ₑ x)

x::EscapeLattice ⊔ y::EscapeLattice = begin
    xf, yf = x.FieldSets, y.FieldSets
    if xf === true || yf === true
        FieldSets = true
    elseif xf === false
        FieldSets = yf
    elseif yf === false
        FieldSets = xf
    else
        xf, yf = xf::FieldsInfo, yf::FieldsInfo
        xn, yn = length(xf), length(yf)
        nmax, nmin = max(xn, yn), min(xn, yn)
        FieldSets = FieldsInfo(undef, nmax)
        for i in 1:nmax
            if i > nmax
                FieldSets[i] = (xn > yn ? xf : yf)[i]
            else
                FieldSets[i] = xf[i] ∪ yf[i]
            end
        end
    end
    return EscapeLattice(
        x.Analyzed | y.Analyzed,
        x.ReturnEscape | y.ReturnEscape,
        x.ThrownEscape | y.ThrownEscape,
        x.EscapeSites ∪ y.EscapeSites,
        FieldSets,
        )
end

x::EscapeLattice ⊓ y::EscapeLattice = begin
    return EscapeLattice(
        x.Analyzed & y.Analyzed,
        x.ReturnEscape & y.ReturnEscape,
        x.ThrownEscape & y.ThrownEscape,
        x.EscapeSites ∩ y.EscapeSites,
        x.FieldSets, # FIXME
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
- `aliaset::IntDisjointSet{Int}`: a disjoint set that represents aliased arguments and SSA values
"""
struct EscapeState
    arguments::Vector{EscapeLattice}
    ssavalues::Vector{EscapeLattice}
    aliasset::IntDisjointSet{Int}
end
function EscapeState(nslots::Int, nargs::Int, nstmts::Int)
    arguments = EscapeLattice[
        1 ≤ i ≤ nargs ? ArgumentReturnEscape() : NotAnalyzed() for i in 1:nslots]
    ssavalues = EscapeLattice[NotAnalyzed() for _ in 1:nstmts]
    aliaset = AliasSet(nslots+nstmts)
    return EscapeState(arguments, ssavalues, aliaset)
end

# we preserve `IRCode` as well just for debugging purpose
const GLOBAL_ESCAPE_CACHE = IdDict{MethodInstance,Tuple{EscapeState,IRCode}}()
__clear_escape_cache!() = empty!(GLOBAL_ESCAPE_CACHE)

const EscapeChange = Pair{Union{Argument,SSAValue},EscapeLattice}
const AliasChange  = Pair{Int,Int}
const Changes      = Vector{Union{EscapeChange,AliasChange}}

const AliasSet = IntDisjointSet{Int}
function alias_idx(@nospecialize(x), ir::IRCode)
    if isa(x, Argument)
        return x.n
    elseif isa(x, SSAValue)
        return x.id + length(ir.argtypes)
    else
        return nothing
    end
end
function alias_val(idx::Int, ir::IRCode)
    n = length(ir.argtypes)
    return idx > n ? SSAValue(idx-n) : Argument(idx)
end
function get_aliases(aliasset::AliasSet, @nospecialize(key), ir::IRCode)
    idx = alias_idx(key, ir)
    idx === nothing && return nothing
    root = find_root!(aliasset, idx)
    if idx ≠ root || aliasset.ranks[idx] > 0
        # the size of this alias set containing `key` is larger than 1,
        # collect the entire alias set
        aliases = Union{Argument,SSAValue}[]
        for i in 1:length(aliasset.parents)
            if aliasset.parents[i] == root
                push!(aliases, alias_val(i, ir))
            end
        end
        return aliases
    else
        return nothing
    end
end

"""
    find_escapes(ir::IRCode, nargs::Int) -> EscapeState

Escape analysis implementation is based on the data-flow algorithm described in the old paper [^MM02].
The analysis works on the lattice of [`EscapeLattice`](@ref) and transitions lattice elements
from the bottom to the top in a _backward_ way, i.e. data flows from usage cites to definitions,
until every lattice gets converged to a fixed point by maintaining a (conceptual) working set
that contains program counters corresponding to remaining SSA statements to be analyzed.
The analysis only manages a single global state that tracks `EscapeLattice` of each argument
and SSA statement, but also note that some flow-sensitivity is encoded as program counters
recorded in the `EscapeSites` property of each each lattice element.

The analysis also collects alias information using an approach, which is inspired by
the escape analysis algorithm explained in yet another old paper [^JVM05].
In addition to managing escape lattice elements, the analysis state also maintains an "alias set",
which is implemented as a disjoint set of aliased arguments and SSA statements.
When the fields of object `x` are known precisely (i.e. `x.FieldSets isa Vector{IdSet{Any}}` holds),
the alias set is updated each time `z = getfield(x, y)` is encountered in a way that `z` is
aliased to all values of `x.FieldSets[y]`, so that escape information imposed on `z` will be
propagated to all the aliased values and `z` can be replaced with an aliased value later.
Note that in a case when the fields of object `x` can't known precisely (i.e. `x.FieldSets` is `true`),
when `z = getfield(x, y)` is analyzed, escape information of `z` is propagated to `x` rather
than any of `x`'s fields, which is the most conservative propagation since escape information
imposed on `x` will end up being propagated to all of its fields anyway at definitions of `x`
(i.e. `:new` expression or `setfield!` call).

[^MM02]: _A Graph-Free approach to Data-Flow Analysis_.
         Markas Mohnen, 2002, April.
         <https://api.semanticscholar.org/CorpusID:28519618>.

[^JVM05]: _Escape Analysis in the Context of Dynamic Compilation and Deoptimization_.
          Thomas Kotzmann and Hanspeter Mössenböck, 2005, June.
          <https://dl.acm.org/doi/10.1145/1064979.1064996>.
"""
function find_escapes(ir::IRCode, nargs::Int)
    (; stmts, sptypes, argtypes) = ir
    nstmts = length(stmts)

    # only manage a single state, some flow-sensitivity is encoded as `EscapeLattice` properties
    state = EscapeState(length(argtypes), nargs, nstmts)
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
                    has_changes = escape_call!(ir, pc, stmt.args, state, changes)
                    if !is_effect_free
                        for x in stmt.args
                            add_escape_change!(x, ir, ThrownEscape(pc), changes)
                        end
                    else
                        has_changes || continue
                    end
                elseif head === :invoke
                    escape_invoke!(ir, pc, stmt.args, state, changes)
                elseif head === :new || head === :splatnew
                    escape_new!(ir, pc, stmt.args, state, changes)
                elseif head === :(=)
                    lhs, rhs = stmt.args
                    if isa(lhs, GlobalRef) # global store
                        add_escape_change!(rhs, ir, AllEscape(), changes)
                    else
                        invalid_escape_assignment!(ir, pc)
                    end
                elseif head === :foreigncall
                    escape_foreigncall!(ir, pc, stmt.args, state, changes)
                elseif head === :throw_undef_if_not # XXX when is this expression inserted ?
                    add_escape_change!(stmt.args[1], ir, ThrownEscape(pc), changes)
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
                    for x in stmt.args
                        add_escape_change!(x, ir, AllEscape(), changes)
                    end
                end
            elseif isa(stmt, ReturnNode)
                if isdefined(stmt, :val)
                    add_escape_change!(stmt.val, ir, ReturnEscape(pc), changes)
                end
            elseif isa(stmt, PhiNode)
                escape_edges!(ir, pc, stmt.values, state, changes)
            elseif isa(stmt, PiNode)
                escape_val!(ir, pc, stmt, state, changes)
            elseif isa(stmt, PhiCNode)
                escape_edges!(ir, pc, stmt.values, state, changes)
            elseif isa(stmt, UpsilonNode)
                escape_val!(ir, pc, stmt, state, changes)
            elseif isa(stmt, GlobalRef) # global load
                add_escape_change!(SSAValue(pc), ir, AllEscape(), changes)
            elseif isa(stmt, SSAValue)
                # NOTE after SROA, we may see SSA value as statement
                info = state.ssavalues[pc]
                add_escape_change!(stmt, ir, info, changes)
            else
                @assert stmt isa GotoNode || stmt isa GotoIfNot || stmt === nothing # TODO remove me
                continue
            end

            isempty(changes) && continue

            anyupdate |= propagate_changes!(state, changes, ir)

            empty!(changes)
        end

        anyupdate || break
    end

    return state
end

# propagate changes, and check convergence
function propagate_changes!(state::EscapeState, changes::Changes, ir::IRCode)
    local anychanged = false

    for change in changes
        if isa(change, EscapeChange)
            anychanged |= propagate_escape_change!(state, change)
            x, info = change
            aliases = get_aliases(state.aliasset, x, ir)
            if aliases !== nothing
                for alias in aliases
                    morechange = EscapeChange(alias, info)
                    anychanged |= propagate_escape_change!(state, morechange)
                end
            end
        else
            anychanged |= propagate_alias_change!(state, change)
        end
    end

    return anychanged
end

function propagate_escape_change!(state::EscapeState, change::EscapeChange)
    x, info = change
    if isa(x, Argument)
        old = state.arguments[x.n]
        new = old ⊔ info
        if old ≠ new
            state.arguments[x.n] = new
            return true
        end
    else
        x = x::SSAValue
        old = state.ssavalues[x.id]
        new = old ⊔ info
        if old ≠ new
            state.ssavalues[x.id] = new
            return true
        end
    end
    return false
end

function propagate_alias_change!(state::EscapeState, change::AliasChange)
    x, y = change
    xroot = find_root!(state.aliasset, x)
    yroot = find_root!(state.aliasset, y)
    if xroot ≠ yroot
        union!(state.aliasset, xroot, yroot)
        return true
    end
    return false
end

function add_escape_change!(@nospecialize(x), ir::IRCode, info::EscapeLattice, changes::Changes)
    if isa(x, Argument) || isa(x, SSAValue)
        if !isbitstype(widenconst(argextype(x, ir)))
            push!(changes, EscapeChange(x, info))
        end
    end
end

function add_alias_change!(@nospecialize(x), @nospecialize(y), ir::IRCode, changes::Changes)
    xidx = alias_idx(x, ir)
    yidx = alias_idx(y, ir)
    if xidx !== nothing && yidx !== nothing
        push!(changes, AliasChange(xidx, yidx))
    end
end

function escape_edges!(ir::IRCode, pc::Int, backedges::Vector{Any},
                       state::EscapeState, changes::Changes)
    info = state.ssavalues[pc]
    for i in 1:length(backedges)
        if isassigned(backedges, i)
            add_escape_change!(backedges[i], ir, info, changes)
        end
    end
end

function escape_val!(ir::IRCode, pc::Int, x, state::EscapeState, changes::Changes)
    if isdefined(x, :val)
        info = state.ssavalues[pc]
        add_escape_change!(x.val, ir, info, changes)
    end
end

function escape_invoke!(ir::IRCode, pc::Int, args::Vector{Any},
                        state::EscapeState, changes::Changes)
    linfo = first(args)::MethodInstance
    cache = get(GLOBAL_ESCAPE_CACHE, linfo, nothing)
    args = args[2:end]
    if cache === nothing
        for x in args
            add_escape_change!(x, ir, AllEscape(), changes)
        end
    else
        (linfostate, #=, ir::IRCode=#) = cache
        retinfo = state.ssavalues[pc] # escape information imposed on the call statement
        method = linfo.def::Method
        nargs = Int(method.nargs)
        for i in 1:length(args)
            arg = args[i]
            if i ≤ nargs
                arginfo = linfostate.arguments[i]
            else # handle isva signature: COMBAK will this be invalid once we take alias information into account ?
                arginfo = linfostate.arguments[nargs]
            end
            isempty(arginfo.ReturnEscape) && invalid_escape_invoke!(ir, linfo)
            info = from_interprocedural(arginfo, retinfo, pc)
            add_escape_change!(arg, ir, info, changes)
        end
    end
end

# reinterpret the escape information imposed on the callee argument (`arginfo`) in the
# context of the caller frame using the escape information imposed on the return value (`retinfo`)
function from_interprocedural(arginfo::EscapeLattice, retinfo::EscapeLattice, pc::Int)
    @assert arginfo.ReturnEscape
    if arginfo.ThrownEscape
        EscapeSites = BitSet(pc)
    else
        EscapeSites = EMPTY_ESCAPE_SITES
    end
    newarginfo = EscapeLattice(
        #=Analyzed=#true, #=ReturnEscape=#false, arginfo.ThrownEscape, EscapeSites,
        # FIXME implement inter-procedural effect-analysis
        # currently, this essentially disables the entire field analysis
        # it might be okay from the SROA point of view, since we can't remove the allocation
        # as far as it's passed to a callee anyway, but still we may want some field analysis
        # in order to stack allocate it
        #=FieldSets=#true)
    if arginfo.EscapeSites === ARGUMENT_ESCAPE_SITES
        # if this is simply passed as the call argument, we can discard the `ReturnEscape`
        # information and just propagate the other escape information
        return newarginfo
    else
        # if this can be returned, we have to merge its escape information with
        # that of the current statement
        return newarginfo ⊔ retinfo
    end
end

@noinline function invalid_escape_invoke!(ir::IRCode, linfo::MethodInstance)
    @eval Main (ir = $ir; linfo = $linfo)
    error("invalid escape lattice element returned from inter-procedural context: inspect `Main.ir` and `Main.linfo`")
end

@noinline function invalid_escape_assignment!(ir::IRCode, pc::Int)
    @eval Main (ir = $ir; pc = $pc)
    error("unexpected assignment found: inspect `Main.pc` and `Main.pc`")
end

function escape_new!(ir::IRCode, pc::Int, args::Vector{Any},
                     state::EscapeState, changes::Changes)
    info = state.ssavalues[pc]
    if info == NotAnalyzed()
        info = NoEscape()
    end
    newinfo = add_fieldsets(info, ir.stmts[pc][:type], pc, args)
    add_escape_change!(SSAValue(pc), ir, newinfo, changes)

    # propagate the escape information of this object to all its fields as well
    # since they can be accessed through the object
    for i in 2:length(args)
        add_escape_change!(args[i], ir, ignore_fieldsets(info), changes)
    end
end

function add_fieldsets(info::EscapeLattice, @nospecialize(typ), pc::Int, args::Vector{Any})
    FieldSets = info.FieldSets
    nfields = fieldcount_noerror(typ)
    if isa(FieldSets, Bool) && !FieldSets
        if nfields === nothing
            # abstract type, can't propagate
            FieldSets = true
        else
            FieldSets = FieldInfo[FieldInfo() for _ in 1:nfields]
        end
    end
    if !isa(FieldSets, Bool)
        @assert isa(nfields, Int) && nfields == length(FieldSets)
        nargs = length(args)
        for i in 1:nfields
            val = nargs < i+1 ? UnintializedField() : args[i+1]
            push!(FieldSets[i], val)
        end
    end
    return EscapeLattice(info, FieldSets)
end

# escape every argument `(args[6:length(args[3])])` and the name `args[1]`
# TODO: we can apply a similar strategy like builtin calls to specialize some foreigncalls
function escape_foreigncall!(ir::IRCode, pc::Int, args::Vector{Any},
                             state::EscapeState, changes::Changes)
    foreigncall_nargs = length((args[3])::SimpleVector)
    name = args[1]
    # if normalize(name) === :jl_gc_add_finalizer_th
    #     # add `FinalizerEscape` ?
    # end
    add_escape_change!(name, ir, ThrownEscape(pc), changes)
    for i in 6:5+foreigncall_nargs
        add_escape_change!(args[i], ir, ThrownEscape(pc), changes)
    end
end

# NOTE error cases will be handled in `find_escapes` anyway, so we don't need to take care of them below
# TODO implement more builtins, make them more accurate
# TODO use `T_IFUNC`-like logic and don't not abuse dispatch ?

function escape_call!(ir::IRCode, pc::Int, args::Vector{Any},
                      state::EscapeState, changes::Changes)
    ft = argextype(first(args), ir, ir.sptypes, ir.argtypes)
    f = singleton_type(ft)
    if isa(f, Core.IntrinsicFunction)
        return false # COMBAK we may break soundness here, e.g. `pointerref`
    end
    result = escape_builtin!(f, ir, pc, args, state, changes)
    if result === false
        return false # nothing to propagate
    elseif result === missing
        # if this call hasn't been handled by any of pre-defined handlers,
        # we escape this call conservatively
        for i in 2:length(args)
            add_escape_change!(args[i], ir, AllEscape(), changes)
        end
        return true
    else
        return true
    end
end

escape_builtin!(@nospecialize(f), _...) = return missing

# safe builtins
escape_builtin!(::typeof(isa), _...) = return false
escape_builtin!(::typeof(typeof), _...) = return false
escape_builtin!(::typeof(Core.sizeof), _...) = return false
escape_builtin!(::typeof(===), _...) = return false
# not really safe, but `ThrownEscape` will be imposed later
escape_builtin!(::typeof(isdefined), _...) = return false
escape_builtin!(::typeof(throw), _...) = return false

function escape_builtin!(::typeof(Core.ifelse), ir::IRCode, pc::Int, args::Vector{Any}, state::EscapeState, changes::Changes)
    length(args) == 4 || return
    f, cond, th, el = args
    info = state.ssavalues[pc]
    condt = argextype(cond, ir)
    if isa(condt, Const) && (cond = condt.val; isa(cond, Bool))
        if cond
            add_escape_change!(th, ir, info, changes)
        else
            add_escape_change!(el, ir, info, changes)
        end
    else
        add_escape_change!(th, ir, info, changes)
        add_escape_change!(el, ir, info, changes)
    end
end

function escape_builtin!(::typeof(typeassert), ir::IRCode, pc::Int, args::Vector{Any}, state::EscapeState, changes::Changes)
    length(args) == 3 || return
    f, obj, typ = args
    info = state.ssavalues[pc]
    add_escape_change!(obj, ir, info, changes)
end

function escape_builtin!(::typeof(tuple), ir::IRCode, pc::Int, args::Vector{Any}, state::EscapeState, changes::Changes)
    escape_new!(ir, pc, args, state, changes)
end

function escape_builtin!(::typeof(getfield), ir::IRCode, pc::Int, args::Vector{Any}, state::EscapeState, changes::Changes)
    length(args) ≥ 3 || return
    info = state.ssavalues[pc]
    if info == NotAnalyzed()
        info = NoEscape()
    end

    obj = args[2]
    if isa(obj, SSAValue)
        FieldSets = state.ssavalues[obj.id].FieldSets
    elseif isa(obj, Argument)
        FieldSets = state.arguments[obj.n].FieldSets
    else
        return
    end
    if isa(FieldSets, Bool)
        if FieldSets
            # the field can't be analyzed, escape the object itself (including all its fields) conservatively
            add_escape_change!(obj, ir, info, changes)
        else
            # this field hasn't been analyzed yet, do nothing for now
        end
    else
        typ = argextype(obj, ir)
        if isa(typ, DataType)
            fld = args[3]
            fldval = try_compute_field(ir, fld)
            fidx = try_compute_fieldidx(typ, fldval)
        else
            fidx = nothing
        end
        if fidx !== nothing
            for x in FieldSets[fidx]
                add_escape_change!(x, ir, info, changes)
                add_alias_change!(x, SSAValue(pc), ir, changes)
            end
        else
            # when the field can't be known precisely,
            # propagate this escape information to all the fields conservatively
            for FieldSet in FieldSets, x in FieldSet
                add_escape_change!(x, ir, info, changes)
                add_alias_change!(x, SSAValue(pc), ir, changes)
            end
        end
    end
end

function escape_builtin!(::typeof(setfield!), ir::IRCode, pc::Int, args::Vector{Any}, state::EscapeState, changes::Changes)
    length(args) ≥ 4 || return

    obj, fld, val = args[2:4]
    if isa(obj, SSAValue)
        objinfo = state.ssavalues[obj.id]
    elseif isa(obj, Argument)
        objinfo = state.arguments[obj.n]
    else
        if isa(obj, GlobalRef)
            add_escape_change!(val, ir, AllEscape(), changes)
            return
        else
            # XXX add_escape_change!(val, ir, AllEscape(), changes) ?
            @goto add_ssa_escape
        end
    end
    FieldSets = objinfo.FieldSets
    typ = argextype(obj, ir)
    if isa(FieldSets, Bool)
        if FieldSets
            # the field analysis on this object was already done and unsuccessful,
            # nothing can't be done here
        else
            nfields = fieldcount_noerror(typ)
            if nfields !== nothing
                FieldSets = FieldInfo[FieldInfo() for _ in 1:nfields]
                @goto add_field
            else
                # fields aren't known precisely
                add_escape_change!(obj, ir, EscapeLattice(objinfo, #=FieldSets=#true), changes)
            end
        end
    else
        @label add_field # the field sets have been initialized, now add the alias information
        if isa(typ, DataType)
            fldval = try_compute_field(ir, fld)
            fidx = try_compute_fieldidx(typ, fldval)
        else
            fidx = nothing
        end
        if fidx !== nothing
            push!(FieldSets[fidx], val)
        else
            # when the field can't be known precisely,
            # add this alias information to all the field sets conservatively
            for FieldSet in FieldSets
                push!(FieldSet, val)
            end
        end
        # update `obj`'s escape information with the new field sets
        add_escape_change!(obj, ir, EscapeLattice(objinfo, FieldSets), changes)
    end
    # propagate `obj`'s escape information to `val` as well
    add_escape_change!(val, ir, ignore_fieldsets(objinfo), changes)

    # propagate escape information imposed on the return value of this `setfield!`
    @label add_ssa_escape
    ssainfo = state.ssavalues[pc]
    if ssainfo == NotAnalyzed()
        ssainfo = NoEscape()
    end
    add_escape_change!(val, ir, ssainfo, changes)
end

# NOTE define fancy package utilities when developing EA as an external package
if !(_TOP_MOD === Core.Compiler)
    include(@__MODULE__, "utils.jl")
end

end # baremodule EscapeAnalysis

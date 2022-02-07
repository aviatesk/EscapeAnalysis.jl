# TODO this file contains many duplications with the inlining analysis code, factor them out

import Core.Compiler:
    MethodInstance, InferenceResult, Signature,
    MethodResultPure, MethodMatchInfo, UnionSplitInfo, ConstCallInfo, InvokeCallInfo,
    call_sig, argtypes_to_type, is_builtin, is_return_type, istopfunction, validate_sparams,
    specialize_method, invoke_rewrite

const Linfo = Union{MethodInstance,InferenceResult}
struct CallInfo
    linfos::Vector{Linfo}
    fully_covered::Bool
end

function resolve_call(ir::IRCode, stmt::Expr, @nospecialize(info))
    sig = call_sig(ir, stmt)
    if sig === nothing
        return missing
    end
    # TODO handle _apply_iterate
    if is_builtin(sig) && sig.f !== invoke
        return false
    end
    # handling corresponding to late_inline_special_case!
    (; f, argtypes) = sig
    if length(argtypes) == 3 && istopfunction(f, :!==)
        return true
    elseif length(argtypes) == 3 && istopfunction(f, :(>:))
        return true
    elseif f === TypeVar && 2 ≤ length(argtypes) ≤ 4 && (argtypes[2] ⊑ Symbol)
        return true
    elseif f === UnionAll && length(argtypes) == 3 && (argtypes[2] ⊑ TypeVar)
        return true
    elseif is_return_type(f)
        return true
    end
    if info isa MethodResultPure
        return true
    elseif info === false
        return missing
    end
    # TODO handle OpaqueClosureCallInfo
    if sig.f === invoke
        isa(info, InvokeCallInfo) || return missing
        return analyze_invoke_call(sig, info)
    elseif isa(info, ConstCallInfo)
        return analyze_const_call(sig, info)
    elseif isa(info, MethodMatchInfo)
        infos = MethodMatchInfo[info]
    elseif isa(info, UnionSplitInfo)
        infos = info.matches
    else # isa(info, ReturnTypeCallInfo), etc.
        return missing
    end
    return analyze_call(sig, infos)
end

function analyze_invoke_call(sig::Signature, info::InvokeCallInfo)
    match = info.match
    if !match.fully_covers
        # TODO: We could union split out the signature check and continue on
        return missing
    end
    result = info.result
    if isa(result, InferenceResult)
        return CallInfo(Linfo[result], true)
    else
        argtypes = invoke_rewrite(sig.argtypes)
        mi = analyze_match(match, length(argtypes))
        mi === nothing && return missing
        return CallInfo(Linfo[mi], true)
    end
end

function analyze_const_call(sig::Signature, cinfo::ConstCallInfo)
    linfos = Linfo[]
    (; call, results) = cinfo
    infos = isa(call, MethodMatchInfo) ? MethodMatchInfo[call] : call.matches
    local fully_covered = true # required to account for potential escape via MethodError
    local signature_union = Bottom
    local j = 0
    for i in 1:length(infos)
        meth = infos[i].results
        if meth.ambig
            # Too many applicable methods
            # Or there is a (partial?) ambiguity
            return missing
        end
        nmatch = Core.Compiler.length(meth)
        if nmatch == 0 # No applicable methods
            # mark this call may potentially throw, and the try next union split
            fully_covered = false
            continue
        end
        for i = 1:nmatch
            j += 1
            result = results[j]
            if result === nothing
                match = Core.Compiler.getindex(meth, i)
                mi = analyze_match(match, length(sig.argtypes))
                mi === nothing && return missing
                push!(linfos, mi)
                signature_union = Union{signature_union, match.spec_types}
            else
                push!(linfos, result)
                signature_union = Union{signature_union, result.linfo.specTypes}
            end
        end
    end
    if fully_covered
        atype = argtypes_to_type(sig.argtypes)
        fully_covered &= atype <: signature_union
    end
    return CallInfo(linfos, fully_covered)
end

function analyze_call(sig::Signature, infos::Vector{MethodMatchInfo})
    linfos = Linfo[]
    local fully_covered = true # required to account for potential escape via MethodError
    local signature_union = Bottom
    for i in 1:length(infos)
        meth = infos[i].results
        if meth.ambig
            # Too many applicable methods
            # Or there is a (partial?) ambiguity
            return missing
        end
        nmatch = Core.Compiler.length(meth)
        if nmatch == 0 # No applicable methods
            # mark this call may potentially throw, and the try next union split
            fully_covered = false
            continue
        end
        for i = 1:nmatch
            match = Core.Compiler.getindex(meth, i)
            mi = analyze_match(match, length(sig.argtypes))
            mi === nothing && return missing
            push!(linfos, mi)
            signature_union = Union{signature_union, match.spec_types}
        end
    end
    if fully_covered
        atype = argtypes_to_type(sig.argtypes)
        fully_covered &= atype <: signature_union
    end
    return CallInfo(linfos, fully_covered)
end

function analyze_match(match::MethodMatch, npassedargs::Int)
    method = match.method
    na = Int(method.nargs)
    if na != npassedargs && !(na > 0 && method.isva)
        # we have a method match only because an earlier
        # inference step shortened our call args list, even
        # though we have too many arguments to actually
        # call this function
        return nothing
    end

    # Bail out if any static parameters are left as TypeVar
    # COMBAK is this needed for escape analysis?
    validate_sparams(match.sparams) || return nothing

    # See if there exists a specialization for this method signature
    mi = specialize_method(match; preexisting=true) # Union{Nothing, MethodInstance}
    return mi
end

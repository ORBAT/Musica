#=
    CanonicalIndexError (since Julia 1.8)
    https://github.com/JuliaLang/julia/pull/43852
=#

function _throw_canonical_error(msg::String, T::Type)
    @static if isdefined(Base, :CanonicalIndexError)
        throw(CanonicalIndexError(msg, T))
    else
        error(msg, T)
    end
end

@static if !isdefined(Base, :CanonicalIndexError)
    const CanonicalIndexError = ErrorException
end

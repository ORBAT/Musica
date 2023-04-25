using MacroTools
"""
    @forward T.x fn[, fn1, ...]

Forward calls to `fn` to the field `x` on type `T`.
Useful for eg. defining new subtypes of `AbstractArray`

    struct MyArray{T} <: AbstractArray{T}
      coll
    end

    @forward MyArray.coll Base.size, Base.getindex, Base.setindex!

Modified from [MacroTools'](https://github.com/FluxML/MacroTools.jl) macro by using the `Base.@propagate_inbounds` macro instead of the internal
`Base.@_propagate_inbounds_meta` macro
"""
macro forward(ex, fs)
  @capture(ex, T_.field_) || error("Syntax: @forward T.x f, g, h")
  T = esc(T)
  fs = isexpr(fs, :tuple) ? map(esc, fs.args) : [esc(fs)]
  :($([:(Base.@propagate_inbounds $f(x::$T, args...; kwargs...) = ($f(x.$field, args...; kwargs...)))
       for f in fs]...);
    nothing)
end
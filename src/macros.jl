using MacroTools
"""
    @forward T.x fn[, fn1, ...]

Forward calls to `fn` to the field `x` on type `T`. Annotates each new method with `Base.@propagate_inbounds`. 
Useful for eg. defining new subtypes of `AbstractArray`

    struct MyArray{T} <: AbstractArray{T}
      coll
    end

    @forward MyArray.coll Base.size, Base.getindex, Base.setindex!

Modified from [MacroTools'](https://github.com/FluxML/MacroTools.jl) macro that only annotates with `@inbounds`
"""
macro forward(ex, fs)
  @capture(ex, T_.field_) || error("Syntax: @forward T.x f, g, h")
  T = esc(T)
  fs = isexpr(fs, :tuple) ? map(esc, fs.args) : [esc(fs)]
  :($([:($f(x::$T, args...; kwargs...) = (Base.@_propagate_inbounds_meta; $f(x.$field, args...; kwargs...)))
       for f in fs]...);
    nothing)
end
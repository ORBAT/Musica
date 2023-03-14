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

export @forward

macro _return_if_nothing(ex, varname)
  :(
    if isnothing($(esc(ex)))
      return $(esc(varname)), nothing
    end
  )
end


const _prettyprint_indent::String = "  "

prettyprint_expr(e, level::Int=0) = prettyprint_expr(stdout, e, level)

function prettyprint_expr(io::IO, e, level::Int=0)
  lvl_indent = repeat(_prettyprint_indent, level)
  args_indent = repeat(_prettyprint_indent, level + 1)
  if isa(e, Expr)
    print(io, "\n", lvl_indent, "Expr(:")
    print(io, e.head, ", ")
    # if e.head in (:if, :ifelse, :block)
    #   print("\n", args_indent)
    # end
    first = true
    for arg in e.args
      if first
        first = false
      else
        print(io, ", ")
      end
      prettyprint_expr(io, arg, level + 1)
    end
    print(io, ")")
  elseif isa(e, Symbol)
    print(io, ":", e)
  elseif isa(e, QuoteNode)
    print(io, "QuoteNode(")
    prettyprint_expr(io, e.value)
    print(io, ")")
  else
    print(io, e)
  end
end

function sprettyprint_expr(e)
  io = IOBuffer()
  prettyprint_expr(io, e)
  io |> take! |> String
end

export prettyprint_expr, sprettyprint_expr

using MacroTools, MLStyle
using MLStyle: @match, @λ
using MacroTools: MacroTools.postwalk
using InteractiveUtils: gen_call_with_extracted_types
using TestItems

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
  fs = Base.isexpr(fs, :tuple) ? map(esc, fs.args) : [esc(fs)]
  :($([:(Base.@propagate_inbounds function $f(x::$T, args...; kwargs...)
    ($f(x.$field, args...; kwargs...))
  end)
       for f in fs]...);
  nothing)
end

export @forward

prettyprint_expr(e; spaces=2, compact=false) = prettyprint_expr(stdout, e, 0; spaces, compact)

prettyprint_expr(io::IO, e::Symbol, level=0; spaces, compact) = print(io, e |> repr)

#=
FIXME: QuoteNodet printtautuu päin vittuja
In [7]: q=(@expand @ifsomething(s.in_iter) do in_iter
            return Iterators.rest(s.full_input, in_iter)
          end);

In [8]: q|>prettyprint_expr

Expr(:block, 
  Expr(:block, 
    Expr(:if, 
      Expr(:call, Musica.issomething, 
        Expr(:., :s, :in_iterQuoteNode(nothing))), 
      Expr(:block, 
        Expr(:(=), :in_iter, 
          Expr(:call, Base.something, 
            Expr(:., :s, :in_iterQuoteNode(nothing)))), 
        Expr(:block, 
          Expr(:return, 
            Expr(:call, 
              Expr(:., :Iterators, :restQuoteNode(nothing)), 
              Expr(:., :s, :full_inputQuoteNode(nothing)), :in_iter)))))))
=#
function prettyprint_expr(io::IO, e::QuoteNode, level=0; spaces, compact)
  str = sprint(dump, e)
  # @debug "prettyprint_expr" str e.value
  print(io, "QuoteNode(", prettyprint_expr(io, e.value, level; spaces, compact), ")")
end
function prettyprint_expr(io::IO, ex::Expr, level; spaces, compact)
  indent = compact ? "" : LazyString("\n", (' '^spaces)^level)
  e = MacroTools.striplines(ex)
  print(io, indent, "Expr(")
  prettyprint_expr(io, e.head, level; spaces, compact)
  print(io, ", ")
  first = true
  for arg in e.args
    if first
      first = false
    else
      print(io, ", ")
    end
    prettyprint_expr(io, arg, level + 1; spaces, compact)
  end
  print(io, ")")
end

function prettyprint_expr(io::IO, e, level=0; spaces, compact)
  print(io, e)
end

sprettyprint_expr(e; compact=false) =
  sprint(prettyprint_expr, e, 0; context=(:compact => compact, :spaces => 2))

export prettyprint_expr, sprettyprint_expr

macro escm(x::Expr)
  @assert x.head === :macrocall
  return esc(Core.eval(__module__, x.args[1])(x.args[2], __module__, x.args[3:end]...))
end

"""
    @__FUNCTION__

Returns the name of the function that called `@__FUNCTION__` as a symbol if possible, or `nothing` otherwise. Note that anonymous functions won't have very pretty names, they'll be something along the lines of `Symbol("#43")`.

```jldoctest
julia> bleb() = @__FUNCTION__;

julia> bleb() |> nameof
:bleb
```

NOTE: this **does not work with macros** as-is, and you have to either escape the call and explicitly refer to the `Musica` module::

```jldoctest
julia> macro A(); esc(:($Musica.@__FUNCTION__)); end;

julia> func() = @A;

julia> func() |> nameof
:func
```

Or use the unexported `Musica.@escm` macro to do it for you:

```jldoctest
julia> macro A2(); :(Musica.@escm @__FUNCTION__); end;

julia> func2() = @A2;

julia> func2() |> nameof
:func2
```

Code lifted from https://github.com/JuliaLang/julia/issues/6733#issuecomment-918792861
"""
macro __FUNCTION__()
  quote
    ($(esc(Expr(:isdefined, :var"#self#"))) ?
     $(esc(:var"#self#")) :
     nothing)
  end
end

export @__FUNCTION__

macro inferret(ex)
  _inferret(ex, (x...) -> (Base.return_types(x...)[1]), __module__)
end

"""
    Musica.@infer_effects(expr)

Infer the effects of calling `expr`.
"""
macro infer_effects(ex)
  _inferret(ex, Core.Compiler.infer_effects, __module__)
end

# NOTE: modified from stdlib's Test._inferred
function _inferret(ex, infer_fn, mod)
  if Meta.isexpr(ex, :ref)
    ex = Expr(:call, :getindex, ex.args...)
  end
  Meta.isexpr(ex, :call) || error("@inferret / @infer_effects requires a call expression")
  farg = ex.args[1]
  if isa(farg, Symbol) && farg !== :.. && first(string(farg)) == '.'
    farg = Symbol(string(farg)[2:end])
    ex = Expr(:call, GlobalRef(Test, :_materialize_broadcasted),
      farg, ex.args[2:end]...)
  end
  quote
    let
      $(
        if any(a -> (Meta.isexpr(a, :kw) || Meta.isexpr(a, :parameters)), ex.args)
          # Has keywords
          args = gensym()
          kwargs = gensym()
          quote
            $(esc(args)), $(esc(kwargs)), result =
              $(esc(Expr(:call, _args_and_call, ex.args[2:end]..., ex.args[1])))
            inftype = $(gen_call_with_extracted_types(
              mod,
              infer_fn,
              :($(ex.args[1])($(args)...; $(kwargs)...)),
            ))
          end
        else
          # No keywords
          quote
            args = ($([esc(ex.args[i]) for i in 2:length(ex.args)]...),)
            # TODO: don't execute the expression here, just do the inference
            result = $(esc(ex.args[1]))(args...)
            inftype = $infer_fn($(esc(ex.args[1])), Base.typesof(args...))
          end
        end
      )

      rettype = result isa Type ? Type{result} : typeof(result)
      (rettype=rettype, inferred=inftype, result=result)
      # rettype <: allow || rettype == typesplit(inftypes[1], allow) || error("return type $rettype does not match inferred return type $(inftypes[1])")
      # result
    end
  end
end

"""
    Musica.@test_inferret somefunction(a, b, c)

Similar to `Test.@inferred`, but tests that the inferred return type is concrete type or a `Union` that's sufficiently small and simple for eg. union splitting to work, and that the return type is a _subtype_ of the inferred type. The logic behind this is that an inferred type of `Union` can be Good Enough™ if it's only got a few arguments that are all concrete.
"""
macro test_inferret(ex)
  ex′ = quote
    return_type, inferred_type, res =
      $(_inferret(ex, (x...) -> (Base.return_types(x...)[1]), __module__))
    if inferred_type isa Union
      Core.Compiler.issimpleenoughtype(inferred_type) ||
        error(
          "Inferred return type union either has too many types, or contains too many \"complex\" types (as defined by the compiler). Type was $inferred_type",
        )
    end

    Musica.all_concrete(inferred_type) || error(
      "Inferred type \"$inferred_type\" is not concrete or is a Union with non-concrete arguments. Non-concretes: $(join(Musica.only_nonconcrete(inferred_type),", "))",
    )

    # QUE: is it even possible for this to not be true?
    return_type <: inferred_type ||
      error("return type $return_type is not a subtype of inferred return type $inferred_type")

    res
  end
end

@testitem "test_inferret" begin
  using StaticArrays
  import Try
  struct Bob end
  let returns_abstract = () -> Base.inferencebarrier([1, 2, 3])::AbstractArray
    @test_throws "is not concrete" Musica.@test_inferret returns_abstract()
  end

  let returns_any = () -> Base.inferencebarrier([1, 2, 3])::Any
    @test_throws "is not concrete" Musica.@test_inferret returns_any()
  end

  let has_large_union = () -> Base.inferencebarrier(66)::Union{Int,Float64,String,Bob}
    @test_throws ErrorException Musica.@test_inferret(has_large_union())
  end

  let has_smol_union = () -> Base.inferencebarrier(66)::Union{Int,Float64,Bob}
    @test Musica.@test_inferret(has_smol_union()) == 66
  end
end

"""
    all_concrete(T)

Returns true if `T` is a concrete type, or a `Union` of concrete types.
"""
function all_concrete(t::Type)
  @match t begin
    t::Union => all(isconcretetype, Base.uniontypes(t))
    t => isconcretetype(t)
  end
end

"""
    only_nonconcrete(Union{Int,Array{Int}})
    only_nonconcrete(Array{Int})
    only_nonconcrete(T)

Returns an array of non-concrete types in `T`. If `T` is a `Union`, every argument is checked. Returns `nothing` if no non-concrete types are found.

```jldoctest
julia> Array{Int} |> Musica.only_nonconcrete
1-element Vector{Any}:
 Array{Int64}

julia> Union{Int,Array{Int}} |> Musica.only_nonconcrete
1-element Vector{Any}:
 Array{Int64}

julia> Array{Int,1} |> Musica.only_nonconcrete

julia> Union{Int,Array{Int,1}} |> Musica.only_nonconcrete

```
"""
function only_nonconcrete(t::Type)
  _empty_to_nothing(x) = isempty(x) ? nothing : x
  @match t begin
    t::Union => filter(!isconcretetype, Base.uniontypes(t)) |> _empty_to_nothing
    #! format: off
    t && if !isconcretetype(t) end => Any[t]
    #! format: on
    _ => nothing
  end
end

# NOTE: "backport" from Julia 1.10: https://github.com/JuliaLang/julia/commit/0e8c0ea26a093c0887a6274036e364493a094a30
# TODO: check if Base.replace_linenums! is defined and use that if it does
replace_linenums!(ex, ln::LineNumberNode) = ex
function replace_linenums!(ex::Expr, ln::LineNumberNode)
  if ex.head === :block || ex.head === :quote
    # replace line number expressions from metadata (not argument literal or inert) position
    map!(ex.args, ex.args) do @nospecialize(x)
      isa(x, Expr) && x.head === :line && length(x.args) == 1 && return Expr(:line, ln.line)
      isa(x, Expr) && x.head === :line && length(x.args) == 2 &&
        return Expr(:line, ln.line, ln.file)
      isa(x, LineNumberNode) && return ln
      return x
    end
  end
  # preserve any linenums inside `esc(...)` guards
  if ex.head !== :escape
    for subex in ex.args
      subex isa Expr && replace_linenums!(subex, ln)
    end
  end
  return ex
end

replace_linenums!(line) = ex -> Expr(:block, line, replace_linenums!(ex, line))

"""
    Musica.@useifdefined(V, fallback=nothing)

Returns the value of `V` if it's defined, or `fallback` otherwise.
"""
macro useifdefined(V, fallback=nothing)
  _useifdefined(__module__, V, fallback)
end

function _useifdefined(mod, V, fallback)
  @esc mod fallback V
  quote
    $(Expr(:isdefined, V)) ? $V : $fallback
  end
end

@testitem "@useifdefined" begin
  @test Musica.@useifdefined(BLERGH, 666) == 666
end

macro WIP()
  :(error(LazyString("not implemented yet.")))
end

macro WIP(msg)
  :(error(LazyString("not implemented yet. TODO: ", $msg)))
end
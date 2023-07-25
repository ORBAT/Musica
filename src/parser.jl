module Parser
using ..Musica
using StaticArrays, Transducers, TestItems, Accessors, AccessorsExtra, ConstructionBase,
  AutoHashEquals, Parameters, Static, TypeUtils, Dictionaries
import Try, TryExperimental
using Try: isok, iserr
using Transducers: Eduction
using ..Musica: @some, some, @WIP, nil, @useifdefined, @>>, @<<

# HUOM: ei peri Functionia, koska muuten Parseritkin sais saman spesialisointisemantiikan ku Function
"""
    Parser.Abstract{Out,In}

Abstract parser type: `Out` the type of its output (eg. `Int`) and `In` is the _element type_ of its input (eg. `Bool`)
"""
abstract type Abstract{Out,In} end

"""
Parser.State{InpIterState, Input}

    Parser.State(input [, input_iter_state])
    Parser.State{InpIterState}(input [, input_iter_state::InpIterState])
    Parser.State{InpIterState,Input}(input::Input [, output::Output, input_iter_state::InpIterState])

## Type parameters

  - `Input` is the input's type
  - `InpIterState` is the type of the iterator state of `Input`, ie. what this would return `let (val, itr_state) = iterate(input); typeof(itr_state) end`
"""
@auto_hash_equals struct State{InpIterState,Input}
  full_input::Input

  # iterator state for full_input. Instead of eg. dropping elements from full_input when parsing it, in_iter_state should be updated. See Iter.WithNextState for a way to iterate something so that you have access to the iterator state in eg a regular for loop.
  in_iter_state::Optional{InpIterState}

  State{InpIterState,Input}(
    full_input::Input,
    in_iter_state::Optional{InpIterState},
  ) where {InpIterState,Input} = new{InpIterState,Input}(full_input, in_iter_state)
end

const S = State

function Base.:(==)(
  a::State{AIS,AIn},
  b::State{BIS,BIn},
) where {AIS,AIn,BIS,BIn}
  isequal(AIS, BIS) &&
    isequal(AIn, BIn) &&
    isequal(remaining_input(a), remaining_input(b))
end

function State(input, in_iter_state::OptOrValue{T}=none) where {T}
  let II = @ifsomething(typeof, in_iter_state, input |> Iter.itr_state_type)
    State{II,typeof(input)}(input, in_iter_state)
  end
end

# TODO[high-prio]: need Parser.Abstract tests that don't only use "pristine" `State`s but also ones that have had some of their input consumed. Some minimal tooling would be nice

Base.eltype(s::State) = s |> input_type |> eltype

@testitem "Parser.State" begin
  Musica.__enable_debug() do
    @test @inferred(Parser.S{Int}(Bool[1, 0])) == Parser.S{Int}(Bool[1, 0])
    @test Parser.S{Int}(Bool[1, 0]) |> Iter.itr_state_type == Int
  end
end

## NOTE: using `@accessor` macro for these (eg `@accessor in_iter_state(s::State) = s.in_iter_state`) resulted in a weird inference problem where the return type of `@set` / `Accessors.set` with any of these accessors wouldn't be concrete

"""
    Parser.in_iter_state(s::State{InpIterState}) isa Optional{InpIterState}

    (Accessors.@set Parser.in_iter_state(s) = 123) isa Parser.State
    Accessors.set(s, Parser.in_iter_state, 123) isa Parser.State
"""
in_iter_state(s::State) = s.in_iter_state

Accessors.set(
  s::State{InpIterState,Input},
  ::typeof(in_iter_state),
  newiterstate,
) where {InpIterState,Input} =
  let NewInpItrState = @ifsomething(typeof, newiterstate, InpIterState)
    State{NewInpItrState,Input}(s.full_input, newiterstate)
  end

"""
    Parser.full_input(s::State{InpIterState, Input}) isa Input

    Accessors.@set Parser.full_input(s) = [1,2,3]
    Accessors.set(s, Parser.full_input, [1,2,3])
"""
full_input(s::State) = s.full_input
Accessors.set(
  s::State{InpIterState,Input},
  ::typeof(full_input),
  newinput,
) where {InpIterState,Input} =
  State{InpIterState,Core.typeof(newinput)}(newinput, s.output, s.in_iter_state)

# TODO[low-prio]: functor struct instead of closure?
copy_field(optic) = (dst, src) -> Accessors.set(dst, optic, optic(src))

function remaining_input(s::State)
  @ifsomething(in_iter_state(s), Iter.Rest(s.full_input)) do in_iter_state
    Iter.Rest(s.full_input, in_iter_state)
  end
end

function Base.iterate(s::State, it_st::Just)
  r = Iter.Rest(s.full_input, it_st)
  iterate(r)
end

function Base.iterate(s::State)
  remaining_input(s) |> iterate
end

# TODO[low-prio]: figure out proper size somehow. Iter.Rest could build this in
Base.IteratorSize(::Type{<:State{InIt,In}} where {InIt}) where {In} =
  Iter._rest_iteratorsize(Base.IteratorSize(In))

Base.isempty(s::State) = s |> remaining_input |> isempty

Iter.try_itr_state_type(
  ::Type{<:State{InIt}},
) where {InIt} =
  @isdefined(InIt) ?
  Try.Ok(InIt) :
  Try.Err(
    "try_itr_state_type(Parser.State): the given `Type{State}` didn't have its `InpIterState` type parameter bound to anything",
  )

macro err_if_inp_empty(ex)
  quote
    isempty($(esc(ex))) && return Error("input is empty")
  end
end

function peel_input(state)
  @WIP
  @err_if_inp_empty(state)
  (val, new_iter_state) = state |> iterate
end

@testitem "Parser.peel_input" begin
  @test Musica.@WIP
  # let s = Parser.S{Nothing}([])
  # end
end

function Base.show(io::IO, s::State{InIt,I}) where {InIt,I}
  print(io, "State{", InIt, ",", I, "}(")
  print(io, s |> remaining_input |> collect)
  print(io, ')')
end

### HUOM: Base.show -metodi ::Type:lle on tyyppipiratismia ja aiheuttaa ilmeisesti ihan vitusti ongelmia.
# https://discourse.julialang.org/t/weird-error-after-defining-base-show-method-for-custom-datatype/83562
# https://github.com/PainterQubits/Unitful.jl/issues/321
# https://discourse.julialang.org/t/broken-base-show-method/48453
# https://github.com/JuliaLang/julia/issues/35643

@testitem "Parser.State accessors" begin
  using AccessorsExtra, Accessors
  s = Parser.State{Bool}([1, 2, 3])
  Accessors.test_getset_laws(Parser.in_iter_state, s, none, 7)
  Accessors.test_getset_laws(Parser.full_input, s, [1, 2, 3], [4, 5, 6])

  @test s |> Parser.remaining_input |> collect == [1, 2, 3]

  let s2 = @set Parser.in_iter_state(s) = Just(2)
    @test s2 |> Parser.remaining_input |> collect == [2, 3]
  end
end

@testitem "Parser.State iteration" begin
  using Accessors, AccessorsExtra
  let s = Parser.State{Bool}([1, 2, 3])
    @test iterate(s) == (1, Just(2))
    @test [x for x in s] == [1, 2, 3]

    let s2 = @set Parser.in_iter_state(s) = Just(2)
      @test [x for x in s2] == [2, 3]
    end
  end
end

output_type(T::Type) = error("no output type for ", T)
input_type(T::Type) = error("no input type for ", T)

input_type(::Type{<:State{InpIterState,Input} where {InpIterState}}) where {Input} =
  @useifdefined(Input, Base.Bottom)

output_type(::Type{<:Abstract{Out}}) where {Out} = Out
input_type(::Type{<:Abstract{Out,In} where {Out}}) where {In} = In

output_type(p) = output_type(p |> typeof)
input_type(p) = input_type(p |> typeof)

struct ParsingError
  msg::Optional{LazyString}

  # NOTE: not a concrete type!
  last_state::Optional{State}
end

const TryErr = Try.Err{ParsingError}

function Error(msg, state=nothing)
  Try.Err(ParsingError(msg, state))
  # @<< state as(Optional) ParsingError(msg) Try.Err
  # # Try.Err(ParsingError(msg, as(Optional, state)))
end

"""
    Parser.Thunk(state_or_thunk, maybe_next_parser)

A `Thunk` is returned by `Parser.Abstract`s (see the [`Parser.Result`](@ref) "constructor" methods). They contain a `State` _or_ a `Thunk`, and a parser. The state in `state_or_thunk` (or, if it's a `Thunk`, the state it resolves to), is either returned as-is if t

  - If `maybe_parser` is `none`, calling the `Parser.Thunk` returns a `Try.Ok` with the state
  - If `maybe_parser` is set, returns `maybe_parser(state)` (which should be a `Parser.Result`)
  - If `state_or_thunk` is another `Thunk`, a new `Thunk` is returned using the result of `state_or_thunk()` as the new `state_or_thunk`, ie. one "layer" of the inner `Thunk` is unwrapped. If `state_or_thunk()` returns a `Try.Err`, that error is returned as-is
"""
struct Thunk{S,P}
  # ATTN: S can be either `State` or `Thunk`!! Would be neat if I could have S<:Union{<:State,<:Thunk} but that doesn't compile because Thunk's not defined yet at that point

  # WIP[parser-output]: tarviiks lisää muutoksia
  state::S
  parser::P
end

# when the Thunk's `state` is actually a `State`, applies the parser to the state and returns whatever the parser returns.
function (th::Thunk{St,NP} where {St<:State,NP})()
  th.parser(th.state)
end

# the Thunk's state is itself a Thunk. Resolves one "layer" of the inner Thunk by returning a new Thunk using `th.state()` as its state. Note that this might still be a Thunk so further rounds of resolving might be necessary.
# NOTE about implementation: Only one layer is resolved so that using a trampoline construct to resolve the whole chain is possible
function (th::Thunk{St} where {St<:Thunk})()
  Try.map(newstate -> Thunk(newstate, th.parser), th.state())
end

const Success{Out,StateOrThunk<:Union{State,Thunk}} = Tuple{Out,StateOrThunk}

# TODO[tests]: `Thunk`

# TODO[low-prio]: these result types are a bit weird and this feels overcomplicated. Maybe rethink at some point
const TryOk{Out,StateOrThunk<:Union{State,Thunk}} = Try.Ok{Success{Out,StateOrThunk}}

# """
#     const Result{Output,StateOrThunk} = Union{Ok{Output,StateOrThunk},Err{StateOrThunk}}

# A `Parser.Abstract` must always return a `Result`: either a [`Try.Ok`](@ref) that contains the output of the parser and the next state or a thunk
# """
const Result{Output,StateOrThunk<:Union{State,Thunk}} = Union{TryOk{Output,StateOrThunk},TryErr}

# Result(state, nextparser=none) = @WIP "Rework Result and Ok types" #Try.Ok(Thunk(state, nextparser))

## WIP[parser-output] tää ei jatkossa enää toimi koska parserin outputtia ei haluta passata eteenpäin tolla tavalla. 
## NOTE: here for convenience so something like `Result(someparser(state), anotherparser)` works
# Result(ok::Try.Ok, nextparser=none) = Result(Try.unwrap(ok), nextparser)

ResultWith(output::OptOrValue, state_or_thunk) = Try.Ok((as(Optional, output), state_or_thunk))
ResultWith(e::ParsingError) = Try.Err(e)
ResultWith(e::TryErr) = e
ResultWith(e::Try.Err) =
  Try.Err(ParsingError(; msg=LazyString("wrapped error: ", e.value)))

"""
    Parser.try_parser_output_type(p::Parser.Abstract, from_input::Parser.State)

Tries to figure out what `p(from_input)` would return. Returns either a `Try.Ok((Out,State{InIt,In}))` or a `Try.Err`. See [`Parser.output_state_type`](@ref) for a version that throws any errors and returns a `State{…}`

## ATTN: this should only fail during development
"""
function try_parser_return_type(
  p::Type{<:Abstract{POut,PIn}},
  from_input::Type{State{InIt,SIn}},
) where {PIn,POut,SIn,InIt}
  if !(eltype(SIn) <: PIn)
    return Try.Err(
      ArgumentError(
        LazyString(
          "try_parser_output_type with incompatible state input eltype and parser input type. State inputeltype: ",
          eltype(SIn),
          " vs parser input: ",
          PIn,
        ),
      ),
    )
  end
  Try.Ok(Success{POut,State{InIt,SIn}})
end

try_parser_return_type(p::Type{<:Abstract}, from_input::Type{<:State}) = Try.Err(
  ArgumentError(
    LazyString(
      "no try_parser_output_type implementation for parser type ", p, " with input type ",
      from_input),
  ),
)

try_parser_return_type(p::Abstract, from_input::State) =
  try_parser_return_type(p |> typeof, from_input |> typeof)

# TODO[tests]: try_parser_output_type

parser_return_type(p, with_input) = try_parser_return_type(p, with_input) |> Try.unwrap

# FIXME: brazen type piracy ahead. I had custom Err & Ok types previously and they had this sort of behavior for ==, and I can't be arsed to fix shit that depended on this behavior so I'll just hack this for now
"""
comparing `Parser.Ok`s has `isequal` semantics
"""
Base.:(==)(a::TryOk, b::TryOk) = isequal(Try.unwrap(a), Try.unwrap(b))

macro err()
  :(return Error())
end

macro err(msg)
  :(return Error($(esc(msg))))
end

struct UsingFn{Out,In,F} <: Abstract{Out,In}
  fn::F
  """
      UsingFn{Out,In}(fn)
  Turns `fn` into a parser `<: Parser.Abstract{Out,In}`. `fn` must be a callable with the signature `Parser.State{Out,<:Any,<:AbstractArray{In}} -> Parser.Result{NewSt,NextParser} where {NewIn, NewSt<:Parser.State{Out,<:Any,<:AbstractArray{<:NewIn}}, NextParser<:Optional{Parser.Abstract}}`
  """
  UsingFn{Out,In}(fn) where {Out,In} = new{Out,In,Core.Typeof(fn)}(fn)
end

# FIXME: check that u.fn() returns a `State` that matches the declared `Out` and `In` types.
(u::UsingFn)(state) = u.fn(state)

# NOTE: doesn't work, but _might_ be close-ish?
##     ERROR: MethodError: Cannot `convert` an object of type 
##     Err{Musica.Parser.ParserError{None}} to an object of type 
## 
##     Union{Err{Musica.Parser.ParserError{var"#s147"}}, 
##     Ok{Musica.Parser.Thunk{var"#s147", var"#s146"}}} where {var"#s147"<:
##     (Musica.Parser.State{Nothing, Bool}), var"#s146"<:(Optional)}
#
# ((u::UsingFn{Out,In})(state)::Result{<:State{Out,In},<:Optional}) where {Out,In} = u.fn(state)

function UsingFn(fn::Musica.Fn)
  (TOut, TIn) = _fntype_to_parser_type_args(typeof(fn))
  UsingFn{TOut,TIn,typeof(fn)}(fn)
end

# TODO[tests]: UsingFn

function _fntype_to_parser_type_args(
  f::Type{F},
) where {OutS,NextP,Out<:Result{OutS,NextP},InS,In<:Tuple{InS},F<:Musica.Fn{Out,In}}
  # NOTE: the parser input type `PIn` has to be the _element type_ of `InS`'s input type, because `Parser.Abstract{Out,In}` is defined so that `In` is the element type of the input
  @WIP "yank out POut"
  let Argtypes = @NamedTuple{output_type::Type{O}, input_type::Type{I}} where {O,I},
    POut = output_type(OutS), PIn = InS |> input_type |> eltype

    Argtypes{POut,PIn}((output_type=POut, input_type=PIn))
  end
end

"""
A `Parser.Abstract` that reads and returns one element from the input as-is.
"""
struct Anything{T} <: Abstract{T,T} end
function (p::Anything{Out})(state::State{II,In}) where {Out,II,In}
  @err_if_inp_empty(state)
  @WIP

  # let (elem, it_state) = iterate(state |> remaining_input)
  #   # NOTE: type annotation here is needed for a properly inferred output type
  #   new_state::(parser_return_type(p, state)) =
  #     ConstructionBase.setproperties(state, (output=elem, in_iter_state=it_state))
  #   return Result(new_state)
  # end
end

@testitem "Parser.Anything" begin
  using StaticArrays, Try
  let p = Parser.Anything{Bool}()
    @test Parser.execute(p, [true, false]) == Try.Ok(Parser.S([false], true))
    @test Parser.execute(p, Bool[]) |> Parser.iserr
  end

  let p = Parser.Anything{SVector{2,Bool}}()
    @test Parser.execute(p, [@SVector([true, false]), @SVector([false, true])]) ==
          Try.Ok(Parser.S([@SVector([false, true])], @SVector([true, false])))
    @test Parser.execute(p, SVector{2,Bool}[]) |> Parser.iserr
  end
end

# TODO[parser]: Seq: parser that repeats Parser.Abstract A until it returns an error. The error is ignored. Sort of like the Kleene star?

"""
    Parser.Seq(parser)

Repeats `parser` until it returns an error. The error is ignored.
"""
struct Seq{Out,In,A<:Abstract{Out,In}} <: Abstract{Out,In}
  parser::A
end

function (seq::Seq)(state)
  @WIP
end

# NOTE[parser]: or SeqUntil? parser that repeats Parser.Abstract A until Parser.Abstract B returns Ok. For a Parser.Abstract A that is a Parser.Abstract{Outp,Inp}, returns a Musica.List{Outp}.
# Returns Err if A returns Err or the input is exhausted before B returns Ok.

# NOTE[parser]: oooooooor Repeated? parser that repeats Parser.Abstract A N times. Returns Err if A returns Err. Output is a Vector (or a List????). 

# TODO[parser]: Lookahead(A): returns Ok if A would match. No output, doesn't consume any input

# TODO[parser] (low prio): Optimist: a parser that takes Parser.Abstract A, and returns a Parser.Abstract that matches like A but turns any Errs into an Ok containing the state in the Err

"""
    Parser.End()

parser that matches the end of the input. No output, should work with any input
"""
struct End <: Abstract{Nothing,Any} end

function (::End)(state)
  ResultWith(
    isempty(state) ? state : Error("expected input end"),
  )
end

@testitem "Parser.End" begin
  using Try
  let p = Parser.End()
    @test Musica.@test_inferret(Parser.execute(p, [])) == Try.Ok(Parser.S{Nothing}([]))
    @test Musica.@test_inferret(Parser.execute(p, [1])) |> Parser.iserr
  end
end

"""
    Parser.Composed(parser_outer, parser_inner)

A `Parser.Composed` is a `Parser.Abstract` that essentially does `parser_outer(parser_inner(state))`: it takes the same input type as `parser_inner`, and has the same output type as `parser_outer`,
"""
struct Composed{
  OuterOut,
  InnerIn,
  OuterIn,
  InnerOut,
  POuter<:Abstract{OuterOut,OuterIn},
  PInner<:Abstract{InnerOut,InnerIn},
} <: Abstract{OuterOut,InnerIn}
  parser_outer::POuter
  parser_inner::PInner
end

function (m::Composed)(state)
  let parser_outer = m.parser_outer,
    parser_inner = m.parser_inner,
    InnerOut = output_type(parser_inner),
    InnerIn = input_type(parser_inner),
    subparser_inp_state = clear_output_of(state, InnerOut)

    # TODO[low-prio]: use a functor struct rather than a closure
    ResultWith(subparser_inp_state,
      Just(
        Parser.UsingFn{InnerOut,InnerIn}(
          state -> begin
            subp_newstate = parser_inner(state)
            ResultWith(subp_newstate, parser_outer)
          end,
        ),
      ))
  end
end

# TODO[low-prio]: any way to make Parsers compose "out of the box", so that p1 ∘ p2 would just be a regular Base.ComposedFunction?

Base.:∘(p1::Abstract, p2::Abstract) = Composed(p1, p2)

# TODO[tests]: Composed

struct Fail <: Abstract{Nothing,Any} end
(::Fail)(@nospecialize(_)) = @err "Parser.Fail always fails"

@testitem "Parser.Composed" begin
  using Accessors
  let pfail = Parser.Fail(),
    panything = Parser.Anything{Int}(),
    panything_disc = Parser.Discard(Parser.Anything{Int}()),
    pclearout = Parser.UsingFn{Int,Any}(state -> ResultWith(clear_output_of(state, Int)))

    p666 = Parser.UsingFn{Int,Int}(state::Parser.State -> ResultWith(@set state.output = 666))
    @test @WIP
  end
end

"""
    Parser.Discard(parser)
    Parser.Discard(Parser.Exact([1,1]))

A `Parser.Abstract` that matches like `parser` but discards its output.
"""
struct Discard{In,P<:Abstract{<:Any,<:In}} <: Abstract{Nothing,In}
  parser::P
end

# FIXME[high-prio]: parsers that don't output anything could maybe be `Parser.Abstract{Bottom,In}`, or is that too hacky? if it was `Bottom`, then the current `try_parser_output_type` seems like it should work "out of the box" because it just requires that the parser's output type is a subtype of the state's output type:
#= 
function try_parser_output_type(
  p::Type{<:Parser.Abstract{Out,In}},
  from_input::Type{State{SOut,InIt,SInp}},
) where {In,SOut,Out<:SOut,SInp,InIt}
=#

const copy_in_iter_state = copy_field(in_iter_state)

# TODO[low-prio]: use a functor struct instead of a closure
_output_discarding_parser_with(origstate, InpType) =
  UsingFn{Nothing,InpType}(state -> ResultWith(copy_in_iter_state(origstate, state)))

function (d::Discard)(state)
  @err_if_inp_empty(state)
  let subparser = d.parser,
    cont_parser = _output_discarding_parser_with(state, input_type(subparser))
    # TODO[low-prio]: figure out if the `Composed` (or something similar) could be stashed in the `Discard` struct when it's constructed instead of building one every time this functor is called
    # NOTE that ∘ creates a Parser.Composed and not a Base.ComposedFunction because right now Parsers don't actually compose
    (cont_parser ∘ subparser)(state)
  end
end

# function (d::Discard)(state)
#   @err_if_inp_empty(state)
#   let subparser = d.parser, cont_parser = _discard_contin_parser(state)
#     SubOut = output_type(subparser)
#     # we need a new state that has an empty output and an output type that suits subparser
#     subparser_inp_state = clear_output_of(state, SubOut)

#     Result(subparser_inp_state,
#       Just(
#         Parser.UsingFn{SubOut,input_type(subparser)}(
#           state -> begin
#             # TODO[low-prio]: explicit type assert for the new state
#             subp_newstate = subparser(state)
#             Result(subp_newstate, cont_parser)
#           end,
#         ),
#       ))
#   end
# end

@testitem "Parser.Discard" begin
  using Try
  let p = Parser.Discard(Parser.Exact([1, 1]))
    @test Parser.execute(p, [1, 1, 0, 0]) == Try.Ok(Parser.S{Nothing}([0, 0]))

    # test that the state's output doesn't change
    @test Parser.execute(p, Parser.S{Vector{Int}}([1, 1, 0, 0], [666, 42])) ==
          Try.Ok(Parser.S{Vector{Int}}([0, 0], [666, 42]))

    @test Parser.execute(p, [5]) |> Parser.iserr
    @test Parser.execute(p, []) |> Parser.iserr
  end
end

const VecOrTuple = Union{AbstractVector{E},Tuple{Vararg{E}}} where {E}

"""
    Parser.Exact([1,0,1,1])

A `Parser.Abstract` that matches an exact pattern in the input.
"""
struct Exact{Elem,T<:AbstractVector{Elem}} <: Abstract{T,Elem}
  Exact{Elem,T}(pattern::T) where {Elem,T} =
    isempty(pattern) ? throw(ArgumentError("pattern cannot be empty")) : new{Elem,T}(pattern)
  pattern::T
end

Exact(pattern) = Exact{eltype(pattern),typeof(pattern)}(pattern)

function (e::Exact)(state)
  @err_if_inp_empty(state)
  remain_inp = state |> remaining_input |> Iter.WithNextState
  ncompared = 0

  # TODO: should this be state.in_iter_state??!!?!? Mmmmmmaybe not, brain no work, but since we're iterating remain_inp which already takes the last iterator state into account, this should actually be totally fine.
  last_itr_state::Optional{Iter.itr_state_type(state)} = none

  for ((inp_elem, in_iter_st), pat_elem) in zip(remain_inp, e.pattern)
    inp_elem == pat_elem || @err lazy"Exact($(e.pattern)) failed, pattern didn't match"
    ncompared += 1
    last_itr_state = in_iter_st
  end

  if ncompared != length(e.pattern)
    @err lazy"Exact($(e.pattern)) failed, input shorter than the pattern"
  end

  @WIP

  # # NOTE: type annotation here is needed for a properly inferred output type
  # new_state::(parser_return_type(e, state)) =
  #   @set iterstate_and_outp(state) = (last_itr_state, e.pattern)

  # Result(new_state)
end

@testitem "Parser.Exact" begin
  using Try: Ok, unwrap
  using Try, Accessors
  let p = Parser.Exact([1, 1])
    @test Musica.@test_inferret(Parser.execute(p, [1, 1])) == Ok(Parser.S(Int[], [1, 1]))
    @test Musica.@test_inferret(Parser.execute(p, [1, 1, 0, 0])) == Ok(Parser.S([0, 0], [1, 1]))
    @test Musica.@test_inferret(Parser.execute(p, [0, 0])) |> Parser.iserr

    let news = Parser.execute(p, [1, 1, 0, 0])
      @test Musica.@test_inferret(
        Parser.execute(Parser.Exact([0, 0]), Try.map(Parser.clear_output_of, news))
      ) == Ok(Parser.S(Int[], [0, 0]))
    end

    let news = Parser.execute(p, [1, 1, 0, 0])
      @test Musica.@test_inferret(Parser.execute(Parser.Exact([1, 0]), news)) |> Parser.iserr
    end

    # TODO[high-prio]: tools that make it easier to test shit with a `State` with a non-`none` `in_iter_state`
    let orig_s = Parser.S{Vector{Int}}([0, 0, 1, 1, 2, 3]),
      s = @set Parser.in_iter_state(orig_s) = 3

      @test Musica.@test_inferret(Parser.execute(p, s)) == Ok(Parser.S(Int[2, 3], [1, 1]))
    end
  end

  let p = Parser.Exact([[1, 1]])
    @test Musica.@test_inferret(Parser.execute(p, [[1, 1]])) ==
          Ok(Parser.S(Vector{Int}[], [[1, 1]]))
    @test Musica.@test_inferret(Parser.execute(p, [[1, 1], [0, 0]])) ==
          Ok(Parser.S([[0, 0]], [[1, 1]]))
  end
end

struct Or{O,I,PA<:Abstract,PB<:Abstract} <: Abstract{O,I}
  pa::PA
  pb::PB
end

function Or(pa::PA, pb::PB) where {In,AOut,BOut,PA<:Abstract{AOut,In},PB<:Abstract{BOut,In}}
  return Or{Base.nonnothingtype(Union{AOut,BOut}),In,PA,PB}(pa, pb)
end

Or(
  pa::PA,
  pb::PB,
  rest::Abstract,
) where {In,AOut,BOut,PA<:Abstract{AOut,In},PB<:Abstract{BOut,In}} =
  Or(Or(pa, pb), rest...)

# # _or käy läpi parsereita kunnes joku niistä palauttaa Ok
# _or(s, p1::Abstract, ps::Abstract...) = _or(s, p1(s), ps...)

# # parseri palautti success --> katkastaan "ketju" ja palautetaan res
# _or(@nospecialize(_), res::Ok, @nospecialize(ps...)) = res
# # parseri failasi, kokeillaan seuraavaa
# _or(s, _::Error, p1::Abstract, ps::Abstract...) = _or(s, p1(s), ps...)

# # loppui parserit kesken --> fail
# _or(@nospecialize(_), @nospecialize(_::Error)) = Error()

# (o::Or)(s) = _or(s, o.pa, o.pb)
(::Or)(s) = @WIP

@testitem "Parser.Or" begin
  p1 = Parser.Exact(Bool[1, 1])
  p2 = Parser.Exact(Bool[0, 0])
  p3 = Parser.Exact(Bool[1, 0])
  let inp = Bool[1, 1, 1, 0]
    @test_broken Parser.execute(Parser.Or(p1, p2), inp) == Parser.Ok(Parser.S([1, 1], [1, 0]))
    @test_broken Parser.execute(Parser.Or(p2, p1), inp) == Parser.Ok(Parser.S([1, 1], [1, 0]))
  end

  let inp = Bool[1, 0, 1, 0]
    @test Parser.execute(Parser.Or(p2, p1), inp) |> Parser.iserr
    @test_broken Musica.@test_inferret(Parser.execute(Parser.Or(
        p1,
        Parser.Or(p2, p3),
      ), inp)) == Parser.Ok(Parser.S([1, 0], [1, 0]))
  end

  # test that Parsers with incompatible input types can't be Or'd
  let pbad = Parser.Exact([[1, 1]])
    @test_throws MethodError Parser.Or(p1, pbad)
  end

  # FIXME: Parser.Or(p1, Parser.UInts{2}()) is borked, because UInts's input type isn't the exact same as p1's, but this should still work since UInts's input type is a supertype of p1's
  @test_broken !isa(Parser.execute(Parser.Or(p1, Parser.UInts{2}()), Bool[]), TryErr)
end

struct And{Out,In,A,B,PA<:Abstract{A,In},PB<:Abstract{B,In}} <: Abstract{Out,In}
  pa::PA
  pb::PB
  # TODO: if A or B is Nothing, then just have the other type param as the output type and not a tuple
  function And(pa::PA, pb::PB) where {A,B,In,PA<:Abstract{A,In},PB<:Abstract{B,In}}
    return new{Tuple{A,B},In,A,B,PA,PB}(pa, pb)
  end
end

# käy parsereita läpi niin kauan ku ne palauttaa Ok. Syöttää aina edellisen palauttaman staten
# seuraavalle
# _and(curr_res::Ok, p::Parser.Abstract, ps::Parser.Abstract...) = _and(p(Try.unwrap(curr_res)), ps...)

# # ketjun viimeinen Ok -> koko paska menee läpi
# _and(s::Ok) = s
# # Err missä tahansa kohtaa ketjua -> fail
# _and(::Err, @nospecialize(ps...)) = Err()

(a::And)(s) = @WIP #_and(Ok(s), a.pa, a.pb)

@testitem "Parser.And" begin
  using Try: Ok
  using Musica.Parser: Error, S, execute
  const inp = Bool[1, 1, 0, 0]
  const p1 = Parser.Exact(Bool[1, 1])
  const p2 = Parser.Exact(Bool[0, 0])
  const p3 = Parser.Or(Parser.Exact(Bool[1, 0]), p2)

  @test_broken execute(Parser.And(p1, p2), inp) == Ok(S((Bool[0, 0], Bool[1, 1]), Any[]))
  @test_broken Musica.@test_inferret(execute(Parser.And(p1, p2), inp)) ==
               Ok(S((Bool[0, 0], Bool[1, 1]), Any[]))

  @test_broken Musica.@test_inferret(execute(Parser.And(p1, p3), inp)) ==
               Ok(S((Bool[0, 0], Bool[1, 1]), Any[]))

  let s = S(Bool[1, 1, 1, 0], 4)
    @test_broken execute(Parser.And(p1, p2), s) == Error()
  end
end

"""
Takes `NCodons` codons from the remaining input in `s`. Returns an iterator of codons, not a `S`
"""
@inline take_codons(s, ::Val{NCodons}) where {NCodons} = @WIP
# s.remaining_input |> @<(Iterators.take(NCodons))

@testitem "Parser.take_codons" begin
  @test_broken Parser.take_codons(Parser.S{Int}([[1, 1, 1], [1, 0, 0], [0, 1, 1]]), Val(2)) |>
               collect == [[1, 1, 1], [1, 0, 0]]
end

"""
Takes `NCodons` codons from the remaining input in `s` and flattens them
"""
@inline function take_codons_flat(s, ::Val{NCodons}) where {NCodons}
  @WIP
  # return s |> @<(take_codons(Val{NCodons}())) |> Iterators.flatten
end

# FIXME: allow specifying the input type so that UInts can be used with eg. Or & And with parsers that take "chunked" (ie split into codons) input, using Union for the input type just doesn't work as intended (because no covariance for parametric types)
struct UInts{NCodons} <: Abstract{UInt,Union{Bool,Vector{Bool}}} end

function (::UInts{NCodons})(s) where {NCodons}
  inp = take_codons_flat(s, Val{NCodons}())
  @WIP

  # inp_rest = s.remaining_input |> @<(Iterators.drop(NCodons))
  # return Ok(prepend_output(s, undigits(inp |> collect), inp_rest))
end

@testitem "Parser.UInts" begin
  using Transducers

  inp = Vector{Bool}[[1, 0, 1, 0], [1, 0, 1, 1], [1, 0, 0, 1], [0, 1, 1, 1], [1, 1, 1, 1]]
  want = inp[1:3] |> Cat() |> collect |> undigits

  # HOX: demo että Parser.UInts toimii sekä "chunkatulla" että flätillä genomilla
  @test_broken Parser.execute(Parser.UInts{3}(), inp) ==
               Parser.Ok(Parser.S(want, [[0, 1, 1, 1], [1, 1, 1, 1]]))

  let inp_flat = inp |> Cat() |> collect
    @test_broken Parser.execute(Parser.UInts{12}(), inp_flat) ==
                 Parser.Ok(Parser.S(want, [0, 1, 1, 1, 1, 1, 1, 1]))
  end
end

"""
    Varints{MaxCodons}
    Varints{3}

Parsii varinttejä, ottaa enintään `MaxCodons` kodonia inputista. `Varints{1}` on vähän pöljä koska se ei enää ole varsinaisesti varint kun se lukee aina vaan tasan yhden kodonin, mutta 🤷.

Failaa jos inputti on tyhjä.

HOX: vaatii inputin muotoa `Vector{Vector{Int}}`
"""

# TODO: MaxCodons -> MaxBits?
## FIXME: input type
struct Varints{MaxCodons} <: Abstract{UInt,AbstractVector{<:VecOrTuple}} end

function (::Varints{MaxCodons})(s) where {MaxCodons}
  @err_if_inp_empty(s)
  @WIP
  # first, rest = Iterators.peel(s.remaining_input)
  # ntaken = 0
  # num = if !_starts_with_1(first)
  #   @view(first[2:end]) |> Musica.undigits
  # else
  #   taken =
  #     rest |>
  #     @<(Iterators.take(MaxCodons - 1)) |> # -1 koska first otettiin jo
  #     @>(Iterators.takewhile(_starts_with_1)) |> collect

  #   ntaken = length(taken)
  #   bits =
  #     taken |>
  #     @>(Iterators.flatmap(x -> @view x[2:end])) |>
  #     collect |>
  #     @<(prepend!(@view first[2:end])) |>
  #     undigits
  # end
  # input_rest = rest |> @<(Iterators.drop(ntaken))
  # return Ok(prepend_output(s, num, input_rest))
end

@inline _starts_with_1(x) = x |> first == x |> eltype |> one

@testitem "Parser.Varints" begin
  using Transducers

  let inp = Vector{Bool}[[1, 0, 1, 0], [1, 0, 1, 1], [1, 0, 0, 1], [0, 1, 1, 1], [1, 1, 1, 1]],
    want2 = [0, 1, 0, 0, 1, 1] |> undigits,
    want3 = [0, 1, 0, 0, 1, 1, 0, 0, 1] |> undigits

    @test_broken Parser.execute(Parser.Varints{2}(), inp) ==
                 Parser.Ok(Parser.S(want2, [[1, 0, 0, 1], [0, 1, 1, 1], [1, 1, 1, 1]]))

    @test_broken Musica.@test_inferret(Parser.execute(Parser.Varints{4}(), inp)) ==
                 Parser.Ok(Parser.S(want3, [[0, 1, 1, 1], [1, 1, 1, 1]]))

    @test Parser.execute(Parser.Varints{4}(), Vector{Bool}[]) |> Parser.iserr
  end

  let inp = Vector{Bool}[[0, 1, 1, 1], [1, 0, 1, 0]], want = UInt(0b111)
    # HOX: 0:lla alkava kodoni tarkottaa vaan että sen jälkeen ei oo tulossa lisää, ei että ees sitä kodonia ei pitäis tulkata 
    @test_broken Parser.execute(Parser.Varints{2}(), inp) ==
                 Parser.Ok(Parser.S(want, [Bool[1, 0, 1, 0]]))
  end
end

# @inline _execute(res) = (@warn("parser with weird output", res, typeof(res)); res)

@inline _execute(res) = Musica.try_lift(res)
# TODO[low-prio]: trampoline-ish loop instead of recursion
@inline _execute(res::TryOk) = res |> Try.unwrap |> _execute
@inline _execute(res::TryErr) = res

# TODO[low-prio]: trampoline-ish loop instead of recursion
@inline _execute(res::Thunk) = _execute(res())
# @inline _execute(res::Thunk) = _execute(res...)

@inline execute(p::Abstract, s::State) = _execute(p(s))
@inline execute(p::Abstract, s::Try.Ok) = s |> Try.unwrap |> p |> _execute
@inline execute(@nospecialize(_::Abstract), @nospecialize(s::Try.Err)) = s
# FIXME[low-prio]: make sure that eltype(inp) matches p's `In` type parameter
@inline execute(p::Abstract{Out}, inp) where {Out} = execute(p, State{Out}(inp))

@inline _bottom_eltype(::Type{T}) where {T} =
  let ET = eltype(T)
    ET == T ? ET : _bottom_eltype(ET)
  end

# module Exports
# for Fn in (
#   :getctx,
#   :output,
#   :remaining_input,
#   :get_parserstack,
#   :getpstack,
#   :output_type,
#   :input_type,
# )
#   @eval Exports begin
#     using ..Parser: $Fn
#     export $Fn
#   end
# end
# end

end

export Parser
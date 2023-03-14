using Transducers, TestItems

#=
############## HUOM HUOM parsereiden mietintää

Olis kyl hyvä jos pystyis jotenkin Transducereita hyödyntämään. Parserihan on tavallaan reducing function: (state::S, input::T)::S

Mut miten parseemisen saa hoidettua laiskasti? Joku Lazy.jl / LazyArrays.jl / tmv on tietty vaihtoehto, mutta voiskohan Transducers auttaa?
--> ei välttis. Tai et sitä voi käyttää parsereiden "sisällä", mut voi olla et se varsinainen thunkkaus pitää tehä jollain muulla, ku parsereilla
    on aika eri tarpeet ku mitä transducereilla. Plus Transducers.jl on sen verran hankalaa koodia että sen syvällisempään tajuamiseen menis varmaan
    yhtä kauan ku homman ite miettimisessä :P

HOX loput mietinnästä scratchin lopussa

=#

const _EductionOr{T} = Union{Transducers.Eduction,T}
const EductionOrArray{T} = _EductionOr{AbstractArray{T}}

"""
Generally a `Parser` takes an `AbstractArray` input, parses it and returns leftover input and the result of the parse.

See [`parser`](@ref) methods
"""
struct Parser{Out,Fn<:Function} <: Function
  fn::Fn
end

Parser{Out}(fn) where {Out} = Parser{Out,typeof(fn)}(fn)

function Parser(fn, ::Type{Out}) where {Out}
  Parser{Out,typeof(fn)}(fn)
end

# HOX FIXME tää on se vanha malli missä parserin inputti oli aina vaan bittejä
function Parser(fn)
  Parser(fn, Nothing)
end

# HUOM: se wanha malli taas
function (p::Parser{Nothing})(inp::EductionOrArray)
  inp |> p.fn
end


function ((p::Parser{T})(inp::EductionOrArray)::Tuple{EductionOrArray,EductionOrArray{T},Bool}) where {T}
  # HOX: jotkut parserifunkkarit ei palauta ok:ta, koska ne ei koskaan failaa
  (input_left, output, maybe_ok...) = inp |> p.fn
  input_left, output, get_value(maybe_ok, true)
end

function parse_n_bits(input, n_bits)
  (input |> Drop(n_bits) |> collect, undigits(input |> Take(n_bits) |> collect))
end

struct ParseUInt{NBits} end

"""
    ParseUInt(nbits)

A [Parser](@ref) that parses `nbits` bits as a little-endian unsigned integer

```jldoctest
julia> Musica.parser(Musica.ParseUInt(2))([1,1,0])
([0], 0x0000000000000003)
```
"""
ParseUInt(nbits) = ParseUInt{nbits}

@inline function parser(::Type{ParseUInt{NBits}}) where {NBits}
  Parser(@<parse_n_bits(NBits))
end

xf_printer(label) =
  Map() do x
    println(label, ":", x, " – ", typeof(x))
    return x  # just return it as-is
  end


@inline function genome_parser(::Type{ParseUInt{NCodons}}) where {NCodons}
  Parser(UInt) do inp
    (
      inp |> Drop(NCodons), inp |>
                            Take(NCodons) |>
                            Cat() |>
                            Musica.LiftToArray() |>
                            Map(undigits)
    )
  end
end

@testitem "ParseUInt" begin
  @test Musica.parser(Musica.ParseUInt(2))([1, 1, 0]) == (Bool[0], 3)
end
"""
    parser(type)

Return a [`Parser`](@ref) for `type`.
"""
function parser(::Type{T}) where {T}
  error("No parser registered for ", T)
end


###########################################################################################
module Parsing

using ..Musica
using StaticArrays, Transducers, TestItems
using Transducers: Eduction

abstract type Parser{Out,In} <: Function end

@inline output_type(::Type{<:Parser{T}}) where {T} = T
@inline output_type(p::Parser) = output_type(typeof(p))

"""
- `Out` on se minkä tyyppinen `output` on jos se on jotain muuta ku `nothing`. Outputin "pohjimmainen tyyppi"
- `OT` on `output`-fieldin "käytännön" tyyppi, eli jotain `<: Optional{Out}`. Välttää sen että output olis abstrakti tyyppi
- `In` on inputin "pohjimmainen tyyppi". Pitäis varmaan olla joku array tmv.
- `IT` on joko `In` tai sit iteraattori
"""
struct State{Out,In,OT<:Optional{Out},IT}
  output::OT
  remaining_input::IT

  function State{Out,In}(o, inp) where {Out,In}
    # HUOM: ks collection_utils Base.convert(::Type{<:Optional{T}}, […])
    # konvertoidaan o Optional:iksi jos ei jo ole
    _o::Optional{Out} = o
    new{Out,In,typeof(_o),typeof(inp)}(_o, inp)
  end

end

State{Out}(inp) where {Out} = State{Out,typeof(inp)}(nothing, inp)
State(o, inp) = State{typeof(o),typeof(inp)}(o, inp)
State(o::Optional{T}, inp) where {T} = State{T,typeof(inp)}(o, inp)

## TODO FIXME: Base.hash

function Base.:(==)(a::State, b::State)
  a.output == b.output &&
    collect(a.remaining_input) == collect(b.remaining_input)
end


function Base.show(io::IO, s::State{O,I}) where {O,I}
  print(io, "State{", I, " -> ", O, "} (")
  show(io, s.output)
  print(io, ", ")
  show(io, collect(s.remaining_input))
  print(io, ")")
end


### HOX: Base.show -metodi ::Type:lle on tyyppipiratismia ja aiheuttaa ilmeisesti ihan vitusti ongelmia.
# https://discourse.julialang.org/t/weird-error-after-defining-base-show-method-for-custom-datatype/83562
# https://github.com/PainterQubits/Unitful.jl/issues/321
# https://discourse.julialang.org/t/broken-base-show-method/48453
# https://github.com/JuliaLang/julia/issues/35643

#= 
function Base.show(io::IO, ::Type{State{O,I,OT,IT}}) where {O,I,OT,IT}
  # print(io, "State{",O,",",I,",",OT,",",IT,"}")

  print(io, "State{", O)
  if !(OT <: O)
    print(io, "=", OT)
  end
  print(io, ",", I)
  if !(IT <: I)
    it_short_name = IT <: Transducers.Eduction ? "Eduction" : string(IT)
    print(io, "=", it_short_name)
  end
  print(io, "}")
end

 =#
#### TODO HOX: TNothing käyttäminen näin tai sit <:Nothingness tmv vetää
#### kääntäjän ikuiseen luuppiin jostain syystä
# function append_output(s::S, o, inp) where {O,I,IT,S<:State{O,I,TNothing{O},IT}}
#   State{O,I,typeof(o),typeof(inp)}(o, inp)
# end

"""
    append_output(state, new_output, new_input)

    State{Out,OT=None} -> State{Out,OT=SSome{Out}} -> State{Tuple{NewOut,Out}, OT=SSome{Tuple{NewOut,Out}}}
"""
function append_output end

"""
append siinä kohdassa kun `State.output isa None`.
Palauttaa `State`n jonka output on vaan `SSome(o)` ja `T` on typeof(o)


**HOX**: `s`:n alkup Output-tyyppi lentää vaan mäkeen, mutta tää on ehkä ok?
"""
function append_output(s::S, o, inp) where {O,I,IT,S<:State{O,I,None,IT}}
  State{typeof(o),I}(SSome(o), inp)
end

"""
append siinä kohdassa kun State.output on joku mikä tahansa arvo (muu kuin Tuple, ks alla).
Tekee tuplen State.output:ista ja o:sta. Eli jos o::NewT, niin Out=Tuple{T, NewT}
"""
function append_output(s::S, o, inp) where {O,I,OT,IT,S<:State{O,I,OT,IT}}
  new_output = map(s.output) do old_outp
    (old_outp, o)
  end
  State{eltype(new_output),I}(new_output, inp)
end

"""
append siinä kohdin kun State.output isa <:Tuple. Pushataan vaan sen vanhan tuplen perään. Tuple{A,B} -> Tuple{A,B,C}
"""
function append_output(s::S, o, inp) where {O,I,S<:State{O,I,<:SSome{<:Tuple}}}
  new_output = map(s.output) do old_outp
    push!!(old_outp, o)
  end
  State{eltype(new_output),I}(new_output, inp)
end


@testitem "append_output" begin
  using Transducers
  let s = Parsing.State{Int}([1, 1, 0])
    concd = Parsing.append_output(s, [1, 1], [6, 6, 6])
    @test concd isa Parsing.State{Vector{Int}}
    @test concd.output == [1, 1]
    @test concd.remaining_input == [6, 6, 6]
  end

  let inp = Bool[1, 0, 1, 0], s = Parsing.State{Vector{Bool},Vector{Bool}}(Bool[], inp)

    s2 = Parsing.append_output(s, [1, 1, 1], s.remaining_input)
    @test s2 isa Parsing.State{O,I,<:SSome{<:Tuple}} where {O,I}
    @test s2.output == (Bool[], [1, 1, 1])
    @test s2.output isa SSome{Tuple{Vector{Bool},Vector{Int}}}

    s3 = Parsing.append_output(s2, [:yee, :yuu], s2.remaining_input)
    @test s3.output == (Bool[], [1, 1, 1], [:yee, :yuu])
    @test s3.output isa SSome{Tuple{Vector{Bool},Vector{Int},Vector{Symbol}}}
  end

  let inp = Bool[1, 0, 1, 0], s = Parsing.State{Vector{Bool},Vector{Bool}}(nothing, inp)

    s2 = Parsing.append_output(s, [1, 1, 1], s.remaining_input)
    @test s2 isa Parsing.State{O,I,<:SSome{<:Vector{<:Integer}}} where {O,I}
    @test s2.output == [1, 1, 1]
    @test s2.output isa SSome{<:Vector{<:Integer}}

    s3 = Parsing.append_output(s2, [:yee, :yuu], s2.remaining_input)
    @test s3.output == ([1, 1, 1], [:yee, :yuu])
    @test s3.output isa SSome{Tuple{Vector{Int},Vector{Symbol}}}
  end
end

# function _concat_output(s::State, o, inp)
#   # @show s
#   # @show typeof(s)
#   # error("FUCK")
#   State((s.output, o), inp)
# end

abstract type Result end

struct Success{S<:State} <: Result
  state::S
end

function Base.:(==)(a::Success, b::Success)
  a.state == b.state
end

function Base.show(io::IO, s::Success)
  print(io, "Success(")
  show(io, s.state)
  print(io, ")")
end

struct Failure <: Result end

macro _failure_if_empty(ex)
  :(isempty($(esc(ex)).remaining_input) && return Failure())
end

"""
A `Parser` that reads one element from the input
"""
struct Anything{T} <: Parser{T,AbstractVector} end
function (::Anything)(state::State)
  @_failure_if_empty(state)
  inp, rest = Iterators.peel(state.remaining_input)
  Success(append_output(state, inp, rest))
end

@testitem "Parsing.Anything" begin
  let p = Parsing.Anything{Bool}()
    @test Parsing.execute(p, [true, false]) == Parsing.Success(Parsing.State(true, [false]))
    @test Parsing.execute(p, []) == Parsing.Failure()
  end
end

struct Seq{N,T,In<:AbstractVector,P<:Parser{T,In}} <: Parser{NTuple{N,T},In}
  p::P
  function Seq{N}(p::P) where {N,T,In,P<:Parser{T,In}}
    new{N,T,In,P}(p)
  end
end

## TODO: Seq

"""
parseri, joka vaatii tarkan patternin
"""
struct Exact{T<:AbstractVector} <: Parser{T,AbstractVector} # FIXME: input-tyyppi
  pattern::T
end

function (e::Exact)(state::State)
  pat_len = length(e.pattern)
  if length(state.remaining_input) < pat_len
    return Failure()
  end

  got = Iterators.take(state.remaining_input, pat_len)

  for (got, pat) = Iterators.zip(got, e.pattern)
    got != pat && return Failure()
  end
  inp_rest = Iterators.drop(state.remaining_input, pat_len)
  Success(append_output(state, e.pattern, inp_rest))
end

@testitem "Parsing.Exact" begin
  let p = Parsing.Exact([1, 1])
    @test Parsing.execute(p, [1, 1]) == Parsing.Success(Parsing.State([1, 1], []))
    @test Parsing.execute(p, [1, 1, 0, 0]) == Parsing.Success(Parsing.State([1, 1], [0, 0]))
    @test Parsing.execute(p, [0, 0]) == Parsing.Failure()
  end

  let p = Parsing.Exact([[1, 1]])
    @test Parsing.execute(p, [[1, 1]]) == Parsing.Success(Parsing.State([[1, 1]], []))
    @test Parsing.execute(p, [[1, 1], [0, 0]]) == Parsing.Success(Parsing.State([[1, 1]], [[0, 0]]))
  end
end

struct Or{O,PA<:Parser,PB<:Parser} <: Parser{O,AbstractVector} # FIXME: input-tyyppi
  pa::PA
  pb::PB
end

function Or(pa::PA, pb::PB) where {A,B,PA<:Parser{A},PB<:Parser{B}}
  Or{Union{A,B},PA,PB}(pa, pb)
end

# _any käy läpi parsereita kunnes joku niistä palauttaa Success. Palauttaa thunkin, jossa p1(s) on resolvattu
_any(s::State, p1::Function, ps::Function...) = () -> _any(s, p1(s), ps...)

# parseri palautti success --> katkastaan "ketju" ja palautetaan res
_any(@nospecialize(_::State), res::Success, @nospecialize(ps...)) = res
# parseri failasi, kokeillaan seuraavaa
_any(s::State, _::Failure, p1::Function, ps::Function...) = () -> _any(s, p1(s), ps...)

# loppui parserit kesken --> fail
_any(@nospecialize(_::State), _::Failure) = Failure()


function (o::Or)(s::State)
  _any(s, o.pa, o.pb)
end

@testitem "Parsing.Or" begin
  inp = Bool[1, 1, 1, 0]
  p1 = Parsing.Exact(Bool[1, 1])
  p2 = Parsing.Exact(Bool[0, 0])
  let s = Parsing.State{Vector{Bool},Vector{Bool}}(nothing, inp)
    @test Parsing.execute(Parsing.Or(p1, p2), s) == Parsing.Success(Parsing.State([1, 1], [1, 0]))
  end

  let s = Parsing.State{Vector{Bool},Vector{Bool}}(nothing, inp)
    @test Parsing.execute(Parsing.Or(p2, p1), s) == Parsing.Success(Parsing.State([1, 1], [1, 0]))
    let out = Parsing.execute(Parsing.Or(p2, p1), s)
      @test out isa Parsing.Success
      @test typeof(out.state.output) <: SSome{Vector{Bool}}
    end
  end

  let s = Parsing.State(Bool[], Bool[1, 0, 1, 0])
    @test Parsing.execute(Parsing.Or(p2, p1), s) == Parsing.Failure()
  end

  # # execute joka ei vaadi State:a
  # @test Parsing.execute(Parsing.Or(p1, p2), inp) == Parsing.Success(Parsing.State([1, 1], [0, 0]))
end


struct And{A,B,PA<:Parser{A},PB<:Parser{B}} <: Parser{Tuple{A,B},AbstractVector}
  pa::PA
  pb::PB
end


@inline first_output_type(::Type{<:And{A}}) where {A} = A

# käy parsereita läpi niin kauan ku ne palauttaa Success. Syöttää aina edellisen palauttaman Staten
# seuraavalle
_all(curr_res::Success, p::Parser, ps::Parser...) = () -> _all(p(curr_res.state), ps...)

#jos eka arg on thunk, palauta thunk jossa kutsutaan _all resolvatulla arvolla
_all(s_thunk::Function, ps...) = () -> _all(s_thunk(), ps...)
# ketjun viimeinen Success -> koko paska menee läpi
_all(s::Success) = s
# Failure missä tahansa kohtaa ketjua -> fail
_all(::Failure, @nospecialize(ps...)) = Failure()


function (a::And)(s::State)
  _all(Success(s), a.pa, a.pb)
end


@testitem "Parsing.And" begin
  using Musica.Parsing: Success, Failure, State, execute
  inp = Bool[1, 1, 0, 0]
  p1 = Parsing.Exact(Bool[1, 1])
  p2 = Parsing.Exact(Bool[0, 0])

  let s = State{Vector{Bool},Vector{Bool}}(nothing, inp)
    @test execute(Parsing.And(p1, p2), s) ==
          Success(State((Bool[1, 1], Bool[0, 0]), Any[]))

    let out = execute(Parsing.And(p1, p2), s)
      @test out isa Success
      @test typeof(out.state.output) == SSome{Tuple{Vector{Bool},Vector{Bool}}}
    end
  end

  # execute shortcut joka muuttaa inp:n stateksi
  @test execute(Parsing.And(p1, p2), inp) == Success(State((Bool[1, 1], Bool[0, 0]), Any[]))

  let s = State(Bool[], Bool[1, 1, 1, 0])
    @test execute(Parsing.And(p1, p2), s) == Failure()
  end


  @test Parsing.first_output_type(Parsing.And(Parsing.UInts{3}(), p2)) == UInt64
end

"""
Takes `NCodons` codons from the remaining input in `s`. Returns an iterator of codons, not a `State`
"""
@inline function take_codons(s::State{O,I}, ::Type{Val{NCodons}}) where {NCodons,O,I}
  s.remaining_input |> @<(Iterators.take(NCodons))
end

@testitem "Parsing.take_codons" begin
  @test Parsing.take_codons(Parsing.State{Int}([[1, 1, 1], [1, 0, 0], [0, 1, 1]]), Val{2}) |>
        collect == [[1, 1, 1], [1, 0, 0]]
end

"""
Takes `NCodons` codons from the remaining input in `s` and flattens them
"""
@inline function take_codons_flat(s::State{O,I}, ::Type{Val{NCodons}}) where {NCodons,O,I}
  s |> @<(take_codons(Val{NCodons})) |> Iterators.flatten
end

struct UInts{NCodons} <: Parser{UInt,AbstractVector} end

function (::UInts{NCodons})(s::State{O,I}) where {NCodons,O,I}
  inp = take_codons_flat(s, Val{NCodons})

  inp_rest = s.remaining_input |> @<(Iterators.drop(NCodons))
  Success(append_output(s, undigits(inp |> collect), inp_rest))
end

@testitem "Parsing.UInts" begin
  using Transducers

  inp = Vector{Bool}[[1, 0, 1, 0], [1, 0, 1, 1], [1, 0, 0, 1], [0, 1, 1, 1], [1, 1, 1, 1]]
  want = inp[1:3] |> Cat() |> collect |> undigits

  # HOX: demo että Parsing.UInts toimii sekä "chunkatulla" että flätillä genomilla
  @test Parsing.execute(Parsing.UInts{3}(), inp) ==
        Parsing.Success(Parsing.State(want, [[0, 1, 1, 1], [1, 1, 1, 1]]))


  let inp_flat = inp |> Cat() |> collect
    @test Parsing.execute(Parsing.UInts{12}(), inp_flat) ==
          Parsing.Success(Parsing.State(want, [0, 1, 1, 1, 1, 1, 1, 1]))
  end

end


"""
    Varints{MaxCodons}
    Varints{3}

Parsii varinttejä, ottaa enintään `MaxCodons` kodonia inputista. `Varints{1}` on vähän pöljä koska se ei enää
ole varsinaisesti varint kun se lukee aina vaan tasan yhden kodonin, mutta 🤷.

Failaa jos inputti on tyhjä.

HOX: vaatii inputin muotoa `Vector{Vector{Int}}`
"""
struct Varints{MaxCodons} <: Parser{UInt,AbstractVector} end
## TODO FIXME: input type


function (::Varints{MaxCodons})(s::State{O,I}) where {MaxCodons,O,I}
  @_failure_if_empty(s)
  first, rest = Iterators.peel(s.remaining_input)
  ntaken = 0
  num::UInt = if !_first_bit_is_1(first)
    @view(first[2:end]) |> Musica.undigits
  else
    taken = rest |>
            @<(Iterators.take(MaxCodons - 1)) |> # -1 koska first otettiin jo
            @>(Iterators.takewhile(_first_bit_is_1)) |> collect

    ntaken = length(taken)
    @info "Varints parsing took more bits" ntaken length(taken)
    bits = taken |>
           @>(Iterators.flatmap(x -> @view x[2:end])) |>
           collect |>
           @<(prepend!(@view first[2:end])) |>
           undigits
  end
  @info "Varints parsed" ntaken num
  input_rest = rest |> @<(Iterators.drop(ntaken))
  Success(append_output(s, num, input_rest))
end

@inline _first_bit_is_1(x) = x[begin] == one(eltype(x))


@testitem "Parsing.Varints" begin
  using Transducers

  let inp = Vector{Bool}[[1, 0, 1, 0], [1, 0, 1, 1], [1, 0, 0, 1], [0, 1, 1, 1], [1, 1, 1, 1]],
    want2 = [0, 1, 0, 0, 1, 1] |> undigits,
    want3 = [0, 1, 0, 0, 1, 1, 0, 0, 1] |> undigits

    @test Parsing.execute(Parsing.Varints{2}(), inp) ==
          Parsing.Success(Parsing.State(want2, [[1, 0, 0, 1], [0, 1, 1, 1], [1, 1, 1, 1]]))

    @test Parsing.execute(Parsing.Varints{4}(), inp) ==
          Parsing.Success(Parsing.State(want3, [[0, 1, 1, 1], [1, 1, 1, 1]]))

    @test Parsing.execute(Parsing.Varints{4}(), []) == Parsing.Failure()
  end

  let inp = Vector{Bool}[[0, 1, 1, 1], [1, 0, 1, 0]], want = UInt(0b111)
    # HOX: 0:lla alkava kodoni tarkottaa vaan että sen jälkeen ei oo tulossa lisää, ei että ees sitä kodonia
    #      ei pitäis tulkata 
    @test Parsing.execute(Parsing.Varints{2}(), inp) == Parsing.Success(Parsing.State(want, [Bool[1, 0, 1, 0]]))
  end

  # let inp_flat = inp |> Cat() |> collect
  #   @test Parsing.execute(Parsing.UInts{12}(), inp_flat) ==
  #         Parsing.Success(Parsing.State(want, [0, 1, 1, 1, 1, 1, 1, 1]))
  # end

  # @test Parsing.execute(Parsing.Varints)
end

_execute(res::Result) = res

function _execute(thunk::Function)::Result
  res = thunk()
  while res isa Function
    res = res()
  end
  res
end

function execute(p::Parser, s::State)::Result
  _execute(p(s))
end

function execute(p::P, inp::In) where {Out,In,P<:Parser{Out}}
  # HOX: kun State luodaan, sen outputin pitää vastata sitä mikä P:stä pullahtaa ekana ulos. Esim. And(p1,
  # p2):ssa tää olis sit p1:n output-tyyppi
  s = State{first_output_type(P),In}(nothing, inp)
  # @info "execute" s typeof(s)
  execute(p, s)
end

@inline first_output_type(::Type{<:Parser{O}}) where {O} = O

@inline first_output_type(p::Parser) = first_output_type(typeof(p))


@inline _bottom_eltype(::Type{T}) where {T} =
  let ET = eltype(T)
    ET == T ? ET : _bottom_eltype(ET)
  end


end
export Parsing
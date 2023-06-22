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
  input_left, output, get_or_else(maybe_ok, true)
end


## TODO: ei ehkä tarvetta?
#= function ((p::Parser{T})((input_left::EductionOrArray, output::EductionOrArray, ok::Bool))::Tuple{EductionOrArray,EductionOrArray,Bool}) where T
  error("WIP")
#=  (input_left, output, maybe_ok...) = inp |> p.fn
 input_left, output, get_or_else(maybe_ok, true) =#
end =#

# function (curr::Parser{T})(previous_parser::Parser{K}) where {T,K}
#     NewT = Base.promote_typejoin(T,K)
#     Parser(NewT) do inp
#     inp_left, prev_outp, ok = inp |> previous_parser
#     if !ok
#       return inp, (prev_outp, nothing), ok
#     end

#     input_rest, curr_outp::T, ok = curr(inp_left)
#     input_rest, (prev_outp, Some(curr_outp)),rm  ok
#   end

#   error("WIP")
# end

struct VarintParser end


function parse_varint()
  error("WIP")
end

# TODO: jotain näitä allaolevia mä varmaan tarviin, mut ehkä turha tehdä vielä ennen ku tiiän tarkalleen mitä haluun :P
# Vaatinee genomin parempaa suunnittelua

#= """
Return a parser that first parses input with `a`, then gives any leftover bits to `b`. If either parser returns `nothing`, consumes no input
and returns `(bits, nothing)`.
"""
function Base.:+(a::Parser, b::Parser)
  Parser() do bits
    bitsleft, a_result = a(bits)
    @_return_if_nothing a_result bits
    bitsleft, b_result = b(bitsleft)
    @_return_if_nothing b_result bits
    bitsleft, (a_result, b_result)
  end
end

function Base.:|(a::Parser, b::Parser)
  error("WIP")
end


@testitem "Parser" begin
  using Transducers
  parse_ones(n) = Musica.Parser() do input
    got_ones = (input |> Take(n) |> collect) == ones(Int, n) ? :has_ones : nothing
    bitsleft = input
    if !isnothing(got_ones)
      bitsleft = input |> Drop(n) |> collect
    end
    bitsleft, got_ones
  end

  parse_zeros(n) = Musica.Parser() do input
    got_zeros = (input |> Take(n) |> collect) == zeros(Int, n) ? :has_zeros : nothing
    bitsleft = input
    if !isnothing(got_zeros)
      bitsleft = input |> Drop(n) |> collect
    end
    bitsleft, got_zeros
  end

  @test (parse_ones(2) + parse_zeros(2))([1,1,0,0]) == ([], (:has_ones, :has_zeros))
  @test (parse_ones(2) + parse_zeros(2))([1,1,1,1]) == ([1,1,1,1], nothing)
  @test (parse_ones(2) + parse_zeros(2))([0,0,1,1]) == ([0,0,1,1], nothing)
  @test Musica.Parser(identity)([1, 1]) == [1, 1]

end
 =#

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

# TODO: varints
#=

## sovella näitä

function readvarint(io::IO, ::Type{T}) where {T<:Integer}
    o = zero(T)
    n = 0
    b = UInt8(0x80)
    while (b & UInt8(0x80)) ≠ 0
        b = read(io, UInt8)
        o |= convert(T, b & 0x7f) << 7n
        n += 1
    end
    o
end

function writevarint(io::IO, x::Integer)
    n = 0
    c = true
    while c
        b = x & 0x7f
        if (x >>>= 7) ≠ 0
            b |= 0x80
        else
            c = false
        end
        n += write(io, UInt8(b))
    end
    n
end


=#

module Parsing

using ..Musica
using StaticArrays
using Transducers
using Transducers: Eduction
using TestItems

abstract type Parser{Out} <: Function end

@inline output_type(::Type{<:Parser{T}}) where {T} = T
@inline output_type(p::Parser) = output_type(typeof(p))

"""
- `Out` on se minkä tyyppinen `output` on jos se on jotain muuta ku `nothing`. Outputin "pohjimmainen tyyppi"
- `OT` on `output`-fieldin "käytännön" tyyppi, eli jotain `<: Optional{Out}`. Välttää sen että output olis abstrakti tyyppi
- `In` on inputin "pohjimmainen tyyppi". Pitäis varmaan olla joku array tmv.
- `IT` on  on joko `In` tai sit `Eduction`. Ts. tällä saa remaining_input:ista lazyn
"""
struct State{Out,In,OT<:Optional{Out},IT<:Union{In,<:Eduction}}
  output::OT
  remaining_input::IT

  function State{Out,In}(o, inp) where {Out,In}
    # HUOM: ks collection_utils Base.convert(::Type{<:Optional{T}}, […])
    # konvertoidaan o Optional:iksi jos ei jo ole
    _o::Optional{Out} = o
    new{Out,In,typeof(_o),typeof(inp)}(_o, inp)
  end

end


State(o, inp) = State{typeof(o),typeof(inp)}(o, inp)
State(o::Optional{T}, inp) where {T} = State{T,typeof(inp)}(o, inp)

## TODO KYS: miksi tää ei toimi???? Tulee vaan jotain "no method matching (Musica.Parsing.State" blah
# function State{Out}(o, inp::In) where {Out,In}
#   State{Out,In,typeof(o),In}(o, inp)
# end


function collect_remaining_input(s::State{O,I,OT,IT})::I where {O,I,OT,IT<:Eduction}
  s.remaining_input |> collect
end

function collect_remaining_input(s::State{O,I,OT,IT})::I where {O,I,OT,IT}
  s.remaining_input
end

function Base.:(==)(a::State, b::State)
  a.output == b.output &&
    Musica.maybe_collect(a.remaining_input) == Musica.maybe_collect(b.remaining_input)
end


function Base.show(io::IO, s::State{O,I}) where {O,I}
  print(io, "State{", I, " -> ", O, "} (")
  show(io, s.output)
  print(io, ", ")
  show(io, Musica.maybe_collect(s.remaining_input))
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

    State{Out,OT=TNothing} -> State{Out,OT=SSome{Out}} -> State{Tuple{NewOut,Out}, OT=SSome{Tuple{NewOut,Out}}}
"""
function append_output end

"""
append siinä kohdassa kun State.output isa TNothing.
Palauttaa `State`n jonka output on vaan `SSome(o)` ja `OT` on typeof(o)
"""
function append_output(s::S, o, inp) where {O,I,IT,S<:State{O,I,<:TNothing,IT}}
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
  let s = Parsing.State(tnothing(Int), [1, 1, 0])
    concd = Parsing.append_output(s, [1, 1], [6, 6, 6])
    @test concd isa Parsing.State{Vector{Int}}
    @test concd.output == [1, 1]
    @test concd.remaining_input == [6, 6, 6]
  end

  let inp = Bool[1, 0, 1, 0], s = Parsing.State{Vector{Bool},Vector{Bool}}(Bool[], inp)

    s2 = Parsing.append_output(s, [1, 1, 1], s.remaining_input |> Drop(1))
    @test s2 isa Parsing.State{O,I,<:SSome{<:Tuple}} where {O,I}
    @test s2.output == (Bool[], [1, 1, 1])
    @test s2.output isa SSome{Tuple{Vector{Bool},Vector{Int}}}

    s3 = Parsing.append_output(s2, [:yee, :yuu], s2.remaining_input |> Drop(1))
    @test s3.output == (Bool[], [1, 1, 1], [:yee, :yuu])
    @test s3.output isa SSome{Tuple{Vector{Bool},Vector{Int},Vector{Symbol}}}
  end

  let inp = Bool[1, 0, 1, 0], s = Parsing.State{Vector{Bool},Vector{Bool}}(tnothing(), inp)

    s2 = Parsing.append_output(s, [1, 1, 1], s.remaining_input |> Drop(1))
    @test s2 isa Parsing.State{O,I,<:SSome{<:Vector{<:Integer}}} where {O,I}
    @test s2.output == [1, 1, 1]
    @test s2.output isa SSome{<:Vector{<:Integer}}

    s3 = Parsing.append_output(s2, [:yee, :yuu], s2.remaining_input |> Drop(1))
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

#=
HUOM const fieldit mutable structeissa
mutable struct Testi
    const bleb::Int
    bb::Int
end
=#

"""
TODO: parseri / matcheri joka vaatii jonkun tarkan patternin, mutta ei lisää mitään outputtia Stateen
"""
struct Exact{T<:AbstractVector} <: Parser{T}
  pattern::T
end

function (e::Exact)(state::S) where {O,R,S<:State{O,R}}
  if isempty(state.remaining_input)
    return Failure()
  end
  pat_len = length(e.pattern)
  inp_rest = state.remaining_input |> Drop(pat_len)
  got::R = state.remaining_input |> Take(pat_len) |> collect
  if got == e.pattern
    Success(append_output(state, e.pattern, inp_rest))
  else
    Failure()
  end
  # end
end

# FIXME: parempi tyyppi <: Parser{???}
# promote_typejoinin tulos olis hyvä
struct Or{O,PA<:Parser,PB<:Parser} <: Parser{O}
  pa::PA
  pb::PB
end

function Or(pa::PA, pb::PB) where {A,B,PA<:Parser{A},PB<:Parser{B}}
  Or{Union{A,B},PA,PB}(pa, pb)
end

# _any käy läpi thunkkeja kunnes joku niistä palauttaa Success.
# res oli thunk. Palautetaan thunk, jossa se resolvataan
_any(p1::Function, ps::Function...) = () -> _any(p1(), ps...)
# res oli Failure, kokeillaan loppuja thunkkeja
_any(::Failure, ps::Function...) = () -> _any(ps...)

# res oli Success -> katkastaan "ketju" ja palautetaan resultti
_any(res::Success, @nospecialize(ps...)) = res

# loppu thunkit kesken -> fail
_any() = Failure()

function (o::Or)(s::State)
  _any(@>(o.pa(s)), @>(o.pb(s)))
end


struct And{A,B,PA<:Parser{A},PB<:Parser{B}} <: Parser{Tuple{A,B}}
  pa::PA
  pb::PB
end


@inline first_output_type(::Type{<:And{A}}) where {A} = A

# käy parsereita läpi niin kauan ku ne palauttaa Success. Syöttää aina edellisen palauttaman Staten seuraavalle.
# vrt _first_of, jossa ei tarvii kuljettaa tota resulttia mukana, koska kaikki sille annettavat parserit saa saman inputin
function _all(curr_res::Success, p::Parser, ps::Parser...)
  _all(p(curr_res.state), ps...)
end

#jos eka arg on thunk, palauta thunk jossa kutsutaan _all_of resolvatulla arvolla
_all(s_thunk::Function, ps...) = () -> _all(s_thunk(), ps...)
# ketjun viimeinen Success -> koko paska menee läpi
_all(s::Success) = s
# Failure missä tahansa kohtaa ketjua -> fail
_all(::Failure, @nospecialize(ps...)) = Failure()


function (a::And)(s::State)
  _all(Success(s), a.pa, a.pb)
end

struct Varints{MaxCodons} <: Parser{UInt} end
## TODO: ota inputista enintään MaxCodons kodonia niin kauan ku kodonin eka bitti on 1

struct UInts{NCodons} <: Parser{UInt} end

@inline function collect_codons(s::State{O,I}, ::Type{Val{NCodons}}) where {NCodons,O,I}
  inp::Vector{_bottom_eltype(I)} = s.remaining_input |>
                                   Take(NCodons) |>
                                   Cat() |>
                                   collect
  inp
end

function (::UInts{NCodons})(s::S) where {NCodons,O,I,S<:State{O,I}}
  inp = collect_codons(s, Val{NCodons})

  inp_rest = s.remaining_input |> Drop(NCodons)
  Success(append_output(s, undigits(inp), inp_rest))
end

@testitem "Parsing.UInts and Varints" begin
  using Transducers

  inp = Vector{Bool}[[1, 0, 1, 0], [1, 1, 1, 1], [1, 0, 0, 0], [0, 1, 1, 1]]
  want = inp[1:3] |> Cat() |> collect |> undigits

  # HOX: demo että Parsing.UInts toimii sekä "chunkatulla" että flätillä genomilla
  @test Parsing.execute(Parsing.UInts{3}(), inp) ==
        Parsing.Success(Parsing.State(want, [[0, 1, 1, 1]]))


  let inp_flat = inp |> Cat() |> collect
    @test Parsing.execute(Parsing.UInts{12}(), inp_flat) ==
          Parsing.Success(Parsing.State(want, [0, 1, 1, 1]))
  end
end

_execute(res::Function) = _execute(res())
_execute(res) = res

function execute(p::Parser, s::State)
  _execute(p(s))
end

function execute(p::P, inp::In) where {Out,In,P<:Parser{Out}}
  # HOX: kun State luodaan, sen outputin pitää vastata sitä mikä P:stä pullahtaa ekana ulos. Esim. And(p1, p2):ssa
  # tää olis sit p1:n output-tyyppi
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
      @test typeof(Musica.maybe_collect(out.state.output)) <: SSome{Vector{Bool}}
    end
  end

  let s = Parsing.State(Bool[], Bool[1, 0, 1, 0])
    @test Parsing.execute(Parsing.Or(p2, p1), s) == Parsing.Failure()
  end

  # # execute joka ei vaadi State:a
  # @test Parsing.execute(Parsing.Or(p1, p2), inp) == Parsing.Success(Parsing.State([1, 1], [0, 0]))
end

@testitem "Parsing.And" begin
  using Test
  using Musica.Parsing: Success, State
  inp = Bool[1, 1, 0, 0]
  p1 = Parsing.Exact(Bool[1, 1])
  p2 = Parsing.Exact(Bool[0, 0])

  let s = State{Vector{Bool},Vector{Bool}}(nothing, inp)
    @test Parsing.execute(Parsing.And(p1, p2), s) ==
          Success(State((Bool[1, 1], Bool[0, 0]), Any[]))

    let out = Parsing.execute(Parsing.And(p1, p2), s)
      @test out isa Parsing.Success
      @test typeof(Musica.maybe_collect(out.state.output)) == SSome{Tuple{Vector{Bool},Vector{Bool}}}
    end
  end

  # execute shortcut joka muuttaa inp:n stateksi
  @test Parsing.execute(Parsing.And(p1, p2), inp) == Success(State((Bool[1, 1], Bool[0, 0]), Any[]))

  let s = State(Bool[], Bool[1, 1, 1, 0])
    @test Parsing.execute(Parsing.And(p1, p2), s) == Parsing.Failure()
  end


  @test Parsing.first_output_type(Parsing.And(Parsing.UInts{3}(), p2)) == UInt64

end


end

export Parsing
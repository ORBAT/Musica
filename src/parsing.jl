using Transducers, TestItems


const _EductionOr{T} = Union{Transducers.Eduction,T}
const EductionOrArray = _EductionOr{AbstractArray}

"""
Generally a `Parser` takes an `AbstractArray` input, parses it and returns leftover input and the result of the parse.

See [`parser`](@ref) methods
"""
struct Parser{Out} <: Function
  fn::Function
end

function Parser(fn, ::Type{Out}) where {Out}
  Parser{Out}(fn)
end

# HOX FIXME tää on se vanha malli missä parserin inputti oli aina vaan bittejä
function Parser(fn)
  Parser(fn, Nothing)
end

# HUOM: se wanha malli taas
function (p::Parser{Nothing})(inp::EductionOrArray)
  inp |> Cat() |> p.fn
end


function ((p::Parser{T})(inp::EductionOrArray)::Tuple{EductionOrArray,T,Bool}) where T
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

function (curr::Parser{T})(previous_parser::Parser{K}) where {T,K}
  Parser{Tuple{K,Maybe{T}}}() do inp
    inp_left, prev_outp::K, ok = inp |> previous_parser
    if !ok
      return inp, (prev_outp, nothing), ok
    end

    input_rest, curr_outp::T, ok = curr(inp_left)
    input_rest, (prev_outp, Some(curr_outp)), ok
  end

  error("WIP")
end

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


@inline function genome_parser(pui::Type{ParseUInt{NCodons}}) where {NCodons}
  Parser(pui) do inp
    (
      inp |> Drop(NCodons), inp |> Musica.LiftToArray() |>
                            Map(@<(Musica.take(NCodons))) |>
                            Map(x -> x |> Cat() |> collect) |>
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
function parser(::Type{T}) where T
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

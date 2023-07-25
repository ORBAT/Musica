using Transducers, StaticArrays, BenchmarkTools, StatsBase, StructArrays, Random, JET, Cthulhu,
  MacroTools, MethodAnalysis, Static, Try, TryExperimental, Accessors, AccessorsExtra,
  MLStyle, TraceFuns, TypeUtils

using Musica

# BenchmarkTools.DEFAULT_PARAMETERS.samples = 30000

xf_printer(label) =
  Map() do x
    println(label, ": ", x)
    return x  # just return it as-is
  end

using Musica.CA: new_state

function CA.new_state(v::Integer)
  @warn "creating Row from Integer in startup.jl"
  new_state(Val(v))
end

test_state = new_state(BitVector, Val(16))
n_generations = 5

const test_ca::CA.ECA = CA.Elementary(110)
const test_ca2::CA.ECA = CA.Elementary(54)

macro _parser_test_values()
  quote
    using Parser: Or, Exact, S
    p1 = Exact(Bool[1, 1])
    p2 = Exact(Bool[0, 0])
    p3 = Exact(Bool[1, 0])
    p4 = Exact(Bool[0, 1])
    parsing_inp_flat = Bool[1, 1, 0, 0]
    s = S(parsing_inp_flat)
    pOr = Or(Or(p3, p4), p1)
  end |> esc
end

using Transducers, StaticArrays, BenchmarkTools, StatsBase, StructArrays, Random, JET, Cthulhu, MacroTools, Musica, MethodAnalysis, Static

# __enable_debug()

# BenchmarkTools.DEFAULT_PARAMETERS.samples = 30000

xf_printer(label) =
  Map() do x
    println(label, ": ", x)
    return x  # just return it as-is
  end

# includet("src/Musica.jl")
# using .Musica

function _track(m::Module, path::String)
  files = [filename for filename in readdir(path, join=true, sort=false) if splitext(filename)[2] === ".jl"]
  j = (x) -> join(x, ", ")
  @info "Telling Revise to track $(j(files)) in module $m"
  trk = (name) -> begin
    Revise.track(m, name)
    name
  end
  trk.(files)
end

# _track(Musica, "src/")
# _track(Musica.GA, "src/GA")

# _track("src/")
# _track("src/GA")

function new_state(::Type{Val{L}}) where {L}
  let bla = zeros(Bool, L)
    bla[1] = 1
    Row{2}(SizedVector{L}(bla))
  end
end

function new_state(::Val{L}) where {L}
  new_state(Val{L})
end

new_state(v::Integer) = new_state(Val(v))

test_state = new_state(Val{16})
n_generations = 5

test_ca = CA.Elementary(110)
test_ca2 = CA.Elementary(54)
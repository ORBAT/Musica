using ImplicitArrays
using Test

include("../src/compat.jl")

@testset "ImplicitArrays.jl" begin
    @testset "BlockMatrix" begin include("block.jl") end
    @testset "InteractionMatrix" begin include("interaction.jl") end
    @testset "FixedValueArray" begin include("fixedvalue.jl") end
    @testset "RowProjectionMatrix" begin include("rowprojection.jl") end
end

using Test, TestItemRunner, Documenter, Musica

@run_package_tests verbose = true

@testset "doctests" begin
  DocMeta.setdocmeta!(Musica, :DocTestSetup, :(using Musica), recursive=true)
  doctest(Musica, manual=false)
end
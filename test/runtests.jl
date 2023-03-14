using Test, TestItemRunner, Documenter, Musica

@testset "Musica" begin
  @run_package_tests verbose = true
  DocMeta.setdocmeta!(Musica, :DocTestSetup, :(using Musica), recursive=true)
  doctest(Musica, manual=false)
end
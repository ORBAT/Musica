using TestItems

@testitem "doctests" begin
  function with_documenter(fn)
    env = "@v#.#"

    if !(env in Base.LOAD_PATH)
      insert!(Base.LOAD_PATH, 2, env)
      @info "changed LOAD_PATH" Base.LOAD_PATH
    end

    __mod = @__MODULE__()
    @eval __mod using Documenter

    try
      @info "running test fn"
      @eval __mod $fn()
      @info "test fn done"
    catch e
      rethrow(e)
    finally
      let idx = findfirst(isequal(env), Base.LOAD_PATH)
        if idx == nothing
          return
        end
        deleteat!(Base.LOAD_PATH, idx)
        @info "reset LOAD_PATH" Base.LOAD_PATH
      end
    end
  end

  with_documenter() do
    DocMeta.setdocmeta!(Musica, :DocTestSetup, :(using Musica); recursive=true)
    doctest(Musica; manual=false)
  end
end
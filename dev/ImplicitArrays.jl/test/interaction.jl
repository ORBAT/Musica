@testset "empty matrix" begin
    A = InteractionMatrix(Int[], Int[], 11)
    @test A isa AbstractArray{Int, 2}
    @test size(A) == (0, 0)
    @test_throws BoundsError A[]
    @test_throws BoundsError A[1]

    A = InteractionMatrix{Int}(Int[], Int[], +)
    @test A isa AbstractArray{Int, 2}
    @test size(A) == (0, 0)
    @test_throws BoundsError A[]
    @test_throws BoundsError A[1]

    A = InteractionMatrix{Float64}(Int[], Int[], /)
    @test A isa AbstractArray{Float64, 2}
    @test size(A) == (0, 0)
    @test_throws BoundsError A[]
    @test_throws BoundsError A[1]
end

@testset "no rowelems" begin
    A = InteractionMatrix(Int[], Int[42, 40, 47], 11)
    @test A isa AbstractArray{Int, 2}
    @test size(A) == (0, 3)
    @test_throws BoundsError A[]
    @test_throws BoundsError A[1]

    A = InteractionMatrix{Int}(Int[], Int[42, 40, 47], +)
    @test A isa AbstractArray{Int, 2}
    @test size(A) == (0, 3)
    @test_throws BoundsError A[]
    @test_throws BoundsError A[1]

    A = InteractionMatrix{Float64}(Int[], Int[42, 40, 47], /)
    @test A isa AbstractArray{Float64, 2}
    @test size(A) == (0, 3)
    @test_throws BoundsError A[]
    @test_throws BoundsError A[1]
end

@testset "no colelems" begin
    A = InteractionMatrix(Int[42, 40, 47], Int[], 11)
    @test A isa AbstractArray{Int, 2}
    @test size(A) == (3, 0)
    @test_throws BoundsError A[]
    @test_throws BoundsError A[1]

    A = InteractionMatrix{Int}(Int[42, 40, 47], Int[], +)
    @test A isa AbstractArray{Int, 2}
    @test size(A) == (3, 0)
    @test_throws BoundsError A[]
    @test_throws BoundsError A[1]

    A = InteractionMatrix{Float64}(Int[42, 40, 47], Int[], /)
    @test A isa AbstractArray{Float64, 2}
    @test size(A) == (3, 0)
    @test_throws BoundsError A[]
    @test_throws BoundsError A[1]
end

@testset "single value" begin
    A = InteractionMatrix(Int[2], Int[42], 11)
    @test A isa AbstractArray{Int, 2}
    @test size(A) == (1, 1)
    @test A[] isa Int
    @test A[] == 11
    @test A[1] isa Int
    @test A[1] == 11
    @test A[1, 1] isa Int
    @test A[1, 1] == 11
    @test_throws BoundsError A[2]
    @test_throws BoundsError A[1, 2]
    @test_throws BoundsError A[2, 1]
    @test_throws BoundsError A[2, 2]
    @test_throws CanonicalIndexError A[] = 13
    @test_throws CanonicalIndexError A[1] = 13
    @test_throws CanonicalIndexError A[1, 1] = 13

    A = InteractionMatrix{Int}(Int[2], Int[42], -)
    @test A isa AbstractArray{Int, 2}
    @test size(A) == (1, 1)
    @test A[] isa Int
    @test A[] == -40
    @test A[1] isa Int
    @test A[1] == -40
    @test A[1, 1] isa Int
    @test A[1, 1] == -40
    @test_throws BoundsError A[2]
    @test_throws BoundsError A[1, 2]
    @test_throws BoundsError A[2, 1]
    @test_throws BoundsError A[2, 2]
    @test_throws CanonicalIndexError A[] = 13
    @test_throws CanonicalIndexError A[1] = 13
    @test_throws CanonicalIndexError A[1, 1] = 13

    A = InteractionMatrix{Int}(Int[42], Int[2], -)
    @test A[1] == 40

    A = InteractionMatrix{Int}(Int[42], Int[2], /)
    @test_throws TypeError A[1]

    A = InteractionMatrix{Float64}(Int[42], Int[2], /)
    @test A isa AbstractArray{Float64, 2}
    @test A[1] isa Float64
    @test A[1] == 21.0
end

@testset "single rowelem" begin
    A = InteractionMatrix(Int[2], Int[42, 40, 47], 11)
    @test A isa AbstractArray{Int, 2}
    @test size(A) == (1, 3)
    @test_throws BoundsError A[]
    @test A[1] isa Int
    @test A[1] == 11
    @test A[2] isa Int
    @test A[2] == 11
    @test A[3] isa Int
    @test A[3] == 11
    @test A[1, 1] isa Int
    @test A[1, 1] == 11
    @test A[1, 2] isa Int
    @test A[1, 2] == 11
    @test A[1, 3] isa Int
    @test A[1, 3] == 11
    @test_throws BoundsError A[4]
    @test_throws BoundsError A[1, 4]
    @test_throws BoundsError A[2, 1]

    A = InteractionMatrix{Int}(Int[2], Int[42, 40, 47], -)
    @test A isa AbstractArray{Int, 2}
    @test size(A) == (1, 3)
    @test_throws BoundsError A[]
    @test A[1] isa Int
    @test A[1] == -40
    @test A[2] isa Int
    @test A[2] == -38
    @test A[3] isa Int
    @test A[3] == -45
    @test A[1, 1] isa Int
    @test A[1, 1] == -40
    @test A[1, 2] isa Int
    @test A[1, 2] == -38
    @test A[1, 3] isa Int
    @test A[1, 3] == -45
    @test_throws BoundsError A[4]
    @test_throws BoundsError A[1, 4]
    @test_throws BoundsError A[2, 1]

    A = InteractionMatrix{Int}(Int[2], Int[42, 40, 47], \)
    @test_throws TypeError A[1]
    @test_throws TypeError A[2]
    @test_throws TypeError A[3]
    @test_throws TypeError A[1, 1]
    @test_throws TypeError A[1, 2]
    @test_throws TypeError A[1, 3]

    A = InteractionMatrix{Float64}(Int[2], Int[42, 40,47], \)
    @test A[1] isa Float64
    @test A[1] == 21.0
    @test A[2] isa Float64
    @test A[2] == 20.0
    @test A[3] isa Float64
    @test A[3] == 23.5
    @test A[1, 1] isa Float64
    @test A[1, 1] == 21.0
    @test A[1, 2] isa Float64
    @test A[1, 2] == 20.0
    @test A[1, 3] isa Float64
    @test A[1, 3] == 23.5
end

@testset "single colelem" begin
    A = InteractionMatrix(Int[42, 40, 47], Int[2], 11)
    @test A isa AbstractArray{Int, 2}
    @test size(A) == (3, 1)
    @test_throws BoundsError A[]
    @test A[1] isa Int
    @test A[1] == 11
    @test A[2] isa Int
    @test A[2] == 11
    @test A[3] isa Int
    @test A[3] == 11
    @test A[1, 1] isa Int
    @test A[1, 1] == 11
    @test A[2, 1] isa Int
    @test A[2, 1] == 11
    @test A[3, 1] isa Int
    @test A[3, 1] == 11
    @test_throws BoundsError A[4]
    @test_throws BoundsError A[4, 1]
    @test_throws BoundsError A[1, 2]

    A = InteractionMatrix{Int}(Int[42, 40, 47], Int[2], -)
    @test A isa AbstractArray{Int, 2}
    @test size(A) == (3, 1)
    @test_throws BoundsError A[]
    @test A[1] isa Int
    @test A[1] == 40
    @test A[2] isa Int
    @test A[2] == 38
    @test A[3] isa Int
    @test A[3] == 45
    @test A[1, 1] isa Int
    @test A[1, 1] == 40
    @test A[2, 1] isa Int
    @test A[2, 1] == 38
    @test A[3, 1] isa Int
    @test A[3, 1] == 45
    @test_throws BoundsError A[4]
    @test_throws BoundsError A[4, 1]
    @test_throws BoundsError A[1, 2]

    A = InteractionMatrix{Int}(Int[42, 40, 47], Int[2], /)
    @test_throws TypeError A[1]
    @test_throws TypeError A[2]
    @test_throws TypeError A[3]
    @test_throws TypeError A[1, 1]
    @test_throws TypeError A[2, 1]
    @test_throws TypeError A[3, 1]

    A = InteractionMatrix{Float64}(Int[42, 40,47], Int[2], /)
    @test A[1] isa Float64
    @test A[1] == 21.0
    @test A[2] isa Float64
    @test A[2] == 20.0
    @test A[3] isa Float64
    @test A[3] == 23.5
    @test A[1, 1] isa Float64
    @test A[1, 1] == 21.0
    @test A[2, 1] isa Float64
    @test A[2, 1] == 20.0
    @test A[3, 1] isa Float64
    @test A[3, 1] == 23.5
end

@testset "ordinary" begin
    A = InteractionMatrix(Int[2, 5], Int[42, 40], 11)
    @test A isa AbstractArray{Int, 2}
    @test size(A) == (2, 2)
    @test_throws BoundsError A[]
    @test A[1] isa Int
    @test A[1] == 11
    @test A[2] isa Int
    @test A[2] == 11
    @test A[3] isa Int
    @test A[3] == 11
    @test A[4] isa Int
    @test A[4] == 11
    @test A[1, 1] isa Int
    @test A[1, 1] == 11
    @test A[2, 1] isa Int
    @test A[2, 1] == 11
    @test A[1, 2] isa Int
    @test A[1, 2] == 11
    @test A[2, 2] isa Int
    @test A[2, 2] == 11

    A = InteractionMatrix{Int}(Int[2, 5], Int[42, 40], -)
    @test A isa AbstractArray{Int, 2}
    @test size(A) == (2, 2)
    @test_throws BoundsError A[]
    @test A[1] isa Int
    @test A[1] == -40
    @test A[2] isa Int
    @test A[2] == -37
    @test A[3] isa Int
    @test A[3] == -38
    @test A[4] isa Int
    @test A[4] == -35
    @test A[1, 1] isa Int
    @test A[1, 1] == -40
    @test A[2, 1] isa Int
    @test A[2, 1] == -37
    @test A[1, 2] isa Int
    @test A[1, 2] == -38
    @test A[2, 2] isa Int
    @test A[2, 2] == -35

    A = InteractionMatrix{Int}(Int[42, 40], Int[2, 5], -)
    @test A isa AbstractArray{Int, 2}
    @test size(A) == (2, 2)
    @test_throws BoundsError A[]
    @test A[1] isa Int
    @test A[1] == 40
    @test A[2] isa Int
    @test A[2] == 38
    @test A[3] isa Int
    @test A[3] == 37
    @test A[4] isa Int
    @test A[4] == 35
    @test A[1, 1] isa Int
    @test A[1, 1] == 40
    @test A[2, 1] isa Int
    @test A[2, 1] == 38
    @test A[1, 2] isa Int
    @test A[1, 2] == 37
    @test A[2, 2] isa Int
    @test A[2, 2] == 35

    A = InteractionMatrix{Int}(Int[42, 40], Int[2, 5], /)
    @test_throws TypeError A[1]
    @test_throws TypeError A[2]
    @test_throws TypeError A[3]
    @test_throws TypeError A[4]
    @test_throws TypeError A[1, 1]
    @test_throws TypeError A[2, 1]
    @test_throws TypeError A[1, 2]
    @test_throws TypeError A[2, 2]

    A = InteractionMatrix{Float64}(Int[42, 40], Int[2, 5], /)
    @test A[1] isa Float64
    @test A[1] == 21.0
    @test A[2] isa Float64
    @test A[2] == 20.0
    @test A[3] isa Float64
    @test A[3] == 8.4
    @test A[4] isa Float64
    @test A[4] == 8.0
    @test A[1, 1] isa Float64
    @test A[1, 1] == 21.0
    @test A[2, 1] isa Float64
    @test A[2, 1] == 20.0
    @test A[1, 2] isa Float64
    @test A[1, 2] == 8.4
    @test A[2, 2] isa Float64
    @test A[2, 2] == 8.0
end

@testset "empty arrays" begin
    A = FixedValueArray(Nothing, 0)
    @test A isa FixedValueArray{DataType, 1}
    @test size(A) == (0,)
    @test length(A) == 0
    @test_throws BoundsError A[]
    @test_throws BoundsError A[1]

    A = FixedValueArray(Nothing, 0, 0)
    @test A isa FixedValueArray{DataType, 2}
    @test size(A) == (0, 0)
    @test length(A) == 0
    @test_throws BoundsError A[]
    @test_throws BoundsError A[1]

    A = FixedValueArray(Nothing, 0, 1)
    @test A isa FixedValueArray{DataType, 2}
    @test size(A) == (0, 1)
    @test length(A) == 0
    @test_throws BoundsError A[]
    @test_throws BoundsError A[1]

    A = FixedValueArray(Nothing, 1, 0)
    @test A isa FixedValueArray{DataType, 2}
    @test size(A) == (1, 0)
    @test length(A) == 0
    @test_throws BoundsError A[]
    @test_throws BoundsError A[1]

    A = FixedValueArray(Nothing, 0, 0, 0)
    @test A isa FixedValueArray{DataType, 3}
    @test size(A) == (0, 0, 0)
    @test length(A) == 0
    @test_throws BoundsError A[]
    @test_throws BoundsError A[1]
end

@testset "0-dimensional arrays" begin
    A = FixedValueArray(Nothing)
    @test A isa FixedValueArray{DataType, 0}
    @test size(A) == ()
    @test length(A) == 1
    @test_throws BoundsError A[0]
    @test A[] == Nothing
    @test_throws CanonicalIndexError A[] = Nothing
    @test A[1] == Nothing
    @test_throws CanonicalIndexError A[1] = Nothing
    @test_throws BoundsError A[2]
end

@testset "1-dimensional arrays" begin
    A = FixedValueArray(42, 3)
    @test A isa FixedValueArray{Int, 1}
    @test size(A) == (3,)
    @test length(A) == 3
    @test_throws BoundsError A[]
    @test_throws CanonicalIndexError A[] = 41
    @test_throws BoundsError A[0]
    @test_throws CanonicalIndexError A[0] = 41
    for e ∈ A
        @test e == 42
    end
    for i ∈ 1:length(A)
        @test A[i] == 42
        @test_throws CanonicalIndexError A[i] = 41
    end
    @test_throws BoundsError A[4]
    @test_throws CanonicalIndexError A[4] = 41
end

@testset "2-dimensional arrays" begin
    A = FixedValueArray(42, 2, 3)
    @test A isa FixedValueArray{Int, 2}
    @test size(A) == (2, 3)
    @test length(A) == 6
    @test_throws BoundsError A[]
    @test_throws CanonicalIndexError A[] = 41
    @test_throws BoundsError A[0]
    @test_throws CanonicalIndexError A[0] = 41
    @test_throws BoundsError A[0, 1]
    @test_throws CanonicalIndexError A[0, 1] = 41
    @test_throws BoundsError A[1, 0]
    @test_throws CanonicalIndexError A[1, 0] = 41
    for e ∈ A
        @test e == 42
    end
    for i ∈ 1:length(A)
        @test A[i] == 42
        @test_throws CanonicalIndexError A[i] = 41
    end
    for i ∈ 1:size(A)[1], j ∈ 1:size(A)[2]
        @test A[i, j] == 42
        @test_throws CanonicalIndexError A[i, j] = 42
    end
    @test_throws BoundsError A[7]
    @test_throws CanonicalIndexError A[7] = 41
    @test_throws BoundsError A[3, 1]
    @test_throws CanonicalIndexError A[0, 1] = 41
    @test_throws BoundsError A[1, 4]
    @test_throws CanonicalIndexError A[1, 0] = 41
end

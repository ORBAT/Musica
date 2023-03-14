@testset "empty matrix" begin
    @test_throws MethodError BlockMatrix(0, 0)

    for A in [
        BlockMatrix(Array{AbstractArray{Int, 2}, 2}(undef, 0, 0)),
        BlockMatrix{Int}(Array{AbstractArray{Int, 2}, 2}(undef, 0, 0)),
        BlockMatrix{Int}(0, 0)
    ]
        @test A isa AbstractArray{Int, 2}
        @test size(A) == (0, 0)
        @test length(A) == 0
        @test_throws BoundsError A[]
        @test_throws BoundsError A[] = 42
        @test_throws BoundsError A[1]
        @test_throws BoundsError A[1] = 42
    end

    @test_throws AssertionError BlockMatrix(0, 0, zeros(Int, 2, 2))
    @test_throws AssertionError BlockMatrix{Int}(0, 0, zeros(Int, 2, 2))
    @test_throws MethodError BlockMatrix{Int}(0, 0, zeros(2, 2))
end

@testset "no rows" begin
    for A in [
        BlockMatrix(Array{AbstractArray{Int, 2}, 2}(undef, 0, 2)),
        BlockMatrix{Int}(Array{AbstractArray{Int, 2}, 2}(undef, 0, 2)),
        BlockMatrix{Int}(0, 2)
    ]
        @test A isa AbstractArray{Int, 2}
        @test size(A) == (0, 2)
        @test length(A) == 0
        @test_throws BoundsError A[]
        @test_throws BoundsError A[] = 42
        @test_throws BoundsError A[1]
        @test_throws BoundsError A[1] = 42
    end

    @test_throws AssertionError BlockMatrix(0, 2, zeros(Int, 2, 2))
    @test_throws AssertionError BlockMatrix{Int}(0, 2, zeros(Int, 2, 2))
    @test_throws MethodError BlockMatrix{Int}(0, 2, zeros(2, 2))
end

@testset "no cols" begin
    for A in [
        BlockMatrix(Array{AbstractArray{Int, 2}, 2}(undef, 2, 0)),
        BlockMatrix{Int}(Array{AbstractArray{Int, 2}, 2}(undef, 2, 0)),
        BlockMatrix{Int}(2, 0)
    ]
        @test A isa AbstractArray{Int, 2}
        @test size(A) == (2, 0)
        @test length(A) == 0
        @test_throws BoundsError A[]
        @test_throws BoundsError A[] = 42
        @test_throws BoundsError A[1]
        @test_throws BoundsError A[1] = 42
    end

    @test_throws AssertionError BlockMatrix(2, 0, zeros(Int, 2, 2))
    @test_throws AssertionError BlockMatrix{Int}(2, 0, zeros(Int, 2, 2))
    @test_throws MethodError BlockMatrix{Int}(2, 0, zeros(2, 2))
end

@testset "single element" begin
    B11 = 42 .* ones(Int, 1, 1)
    B = Array{AbstractArray{Int, 2}, 2}(undef, 1, 1)
    B[1] = B11

    for (i, A) in enumerate([
        BlockMatrix(B),
        BlockMatrix{Int}(B),
        BlockMatrix(1, 1, B11),
        BlockMatrix{Int}(1, 1, B11)
    ])
        @test A isa AbstractArray{Int, 2}
        @test size(A) == (1, 1)
        @test length(A) == 1
        A[] = 42 + i
        @test A[] isa Int
        @test A[] == B11[] == 42 + i
        A[1] = 43 + i
        @test A[1] isa Int
        @test A[1] == B11[1] == 43 + i
        A[1, 1] = 44 + i
        @test A[1, 1] isa Int
        @test A[1, 1] == B11[1, 1] == 44 + i
        @test_throws BoundsError A[0]
        @test_throws BoundsError A[0, 0]
        @test_throws BoundsError A[0, 1]
        @test_throws BoundsError A[1, 0]
        @test_throws BoundsError A[2]
        @test_throws BoundsError A[1, 2]
        @test_throws BoundsError A[2, 1]
        @test_throws BoundsError A[2, 2]
        @test_throws BoundsError A[0] = 42
        @test_throws BoundsError A[0, 0] = 42
        @test_throws BoundsError A[0, 1] = 42
        @test_throws BoundsError A[1, 0] = 42
        @test_throws BoundsError A[2] = 42
        @test_throws BoundsError A[1, 2] = 42
        @test_throws BoundsError A[2, 1] = 42
        @test_throws BoundsError A[2, 2] = 42
    end

    @test_throws AssertionError BlockMatrix{Int}(1, 1)
    @test_throws AssertionError BlockMatrix(1, 1, B11, B11)
    @test_throws AssertionError BlockMatrix{Int}(1, 1, B11, B11)
    @test_throws MethodError BlockMatrix{Float64}(1, 1, B11)
end

@testset "single row" begin
    B11 = [1 2]
    B12 = [3 4]
    B = Array{AbstractArray{Int, 2}, 2}(undef, 1, 2)
    B[1] = B11
    B[2] = B12

    for (i, A) in enumerate([
        BlockMatrix(B),
        BlockMatrix{Int}(B),
        BlockMatrix(1, 2, B11, B12),
        BlockMatrix{Int}(1, 2, B11, B12)
    ])
        @test A isa AbstractArray{Int, 2}
        @test size(A) == (1, 4)
        @test length(A) == 4
        for j in 1:4
            A[j] = 42i + j
            @test A[j] isa Int
            @test A[j] == 42i + j
            A[1, j] = 42i + j + 1
            @test A[1, j] isa Int
            @test A[1, j] == 42i + j + 1
        end
        @test_throws BoundsError A[]
        @test_throws BoundsError A[0]
        @test_throws BoundsError A[0, 0]
        @test_throws BoundsError A[0, 1]
        @test_throws BoundsError A[1, 0]
        @test_throws BoundsError A[5]
        @test_throws BoundsError A[1, 5]
        @test_throws BoundsError A[2, 1]
        @test_throws BoundsError A[] = 42
        @test_throws BoundsError A[0] = 42
        @test_throws BoundsError A[0, 0] = 42
        @test_throws BoundsError A[0, 1] = 42
        @test_throws BoundsError A[1, 0] = 42
        @test_throws BoundsError A[5] = 42
        @test_throws BoundsError A[1, 5] = 42
        @test_throws BoundsError A[2, 1] = 42
    end

    @test_throws AssertionError BlockMatrix{Int}(1, 2)
    @test_throws AssertionError BlockMatrix(1, 2, B11)
    @test_throws AssertionError BlockMatrix{Int}(1, 2, B11)
    @test_throws AssertionError BlockMatrix(1, 2, B11, B12, B12)
    @test_throws AssertionError BlockMatrix{Int}(1, 2, B11, B12, B12)
    @test_throws MethodError BlockMatrix{Float64}(1, 2, B11)
end

@testset "single col" begin
    B11 = reshape([1, 2], (2, 1))
    B21 = reshape([3, 4], (2, 1))
    B = Array{AbstractArray{Int, 2}, 2}(undef, 2, 1)
    B[1] = B11
    B[2] = B21

    for (i, A) in enumerate([
        BlockMatrix(B),
        BlockMatrix{Int}(B),
        BlockMatrix(2, 1, B11, B21),
        BlockMatrix{Int}(2, 1, B11, B21)
    ])
        @test A isa AbstractArray{Int, 2}
        @test size(A) == (4, 1)
        @test length(A) == 4
        for j in 1:4
            A[j] = 42i + j
            @test A[j] isa Int
            @test A[j] == 42i + j
            A[j, 1] = 42i + j + 1
            @test A[j, 1] isa Int
            @test A[j, 1] == 42i + j + 1
        end
        @test_throws BoundsError A[]
        @test_throws BoundsError A[0]
        @test_throws BoundsError A[0, 0]
        @test_throws BoundsError A[0, 1]
        @test_throws BoundsError A[1, 0]
        @test_throws BoundsError A[5]
        @test_throws BoundsError A[5, 1]
        @test_throws BoundsError A[1, 2]
        @test_throws BoundsError A[] = 42
        @test_throws BoundsError A[0] = 42
        @test_throws BoundsError A[0, 0] = 42
        @test_throws BoundsError A[0, 1] = 42
        @test_throws BoundsError A[1, 0] = 42
        @test_throws BoundsError A[5] = 42
        @test_throws BoundsError A[5, 1] = 42
        @test_throws BoundsError A[1, 2] = 42
    end

    @test_throws AssertionError BlockMatrix{Int}(2, 1)
    @test_throws AssertionError BlockMatrix(2, 1, B11)
    @test_throws AssertionError BlockMatrix{Int}(2, 1, B11)
    @test_throws AssertionError BlockMatrix(2, 1, B11, B21, B21)
    @test_throws AssertionError BlockMatrix{Int}(2, 1, B11, B21, B21)
    @test_throws MethodError BlockMatrix{Float64}(2, 1, B11)
end

@testset "single block" begin
    B11 = [1 2 3; 4 5 6]
    B = Array{AbstractArray{Int, 2}, 2}(undef, 1, 1)
    B[1] = B11

    for (i, A) in enumerate([
        BlockMatrix(B),
        BlockMatrix{Int}(B),
        BlockMatrix(1, 1, B11),
        BlockMatrix{Int}(1, 1, B11)
    ])
        @test A isa AbstractArray{Int, 2}
        @test size(A) == (2, 3)
        @test length(A) == 6
        for row in 1:2
            for col in 1:3
                A[row * col] = 42i + row * col
                @test A[row * col] isa Int
                @test A[row * col] == 42i + row * col
                A[row, col] = 42i + row * col + 1
                @test A[row, col] isa Int
                @test A[row, col] == 42i + row * col + 1
            end
        end
        @test_throws BoundsError A[]
        @test_throws BoundsError A[0]
        @test_throws BoundsError A[0, 0]
        @test_throws BoundsError A[0, 1]
        @test_throws BoundsError A[1, 0]
        @test_throws BoundsError A[7]
        @test_throws BoundsError A[1, 4]
        @test_throws BoundsError A[3, 1]
        @test_throws BoundsError A[] = 42
        @test_throws BoundsError A[0] = 42
        @test_throws BoundsError A[0, 0] = 42
        @test_throws BoundsError A[0, 1] = 42
        @test_throws BoundsError A[1, 0] = 42
        @test_throws BoundsError A[7] = 42
        @test_throws BoundsError A[1, 4] = 42
        @test_throws BoundsError A[3, 1] = 42
    end

    @test_throws AssertionError BlockMatrix{Int}(1, 1)
    @test_throws AssertionError BlockMatrix(1, 1, B11, B11)
    @test_throws AssertionError BlockMatrix{Int}(1, 1, B11, B11)
    @test_throws MethodError BlockMatrix{Float64}(1, 1, B11)
end

@testset "single block row" begin
    B11 = [1 2 3; 7 8 9]
    B12 = [4 5 6; 10 11 12]
    B = Array{AbstractArray{Int, 2}, 2}(undef, 1, 2)
    B[1] = B11
    B[2] = B12

    for (i, A) in enumerate([
        BlockMatrix(B),
        BlockMatrix{Int}(B),
        BlockMatrix(1, 2, B11, B12),
        BlockMatrix{Int}(1, 2, B11, B12)
    ])
        @test A isa AbstractArray{Int, 2}
        @test size(A) == (2, 6)
        @test length(A) == 12
        for row in 1:2
            for col in 1:6
                A[row * col] = 42i + row * col
                @test A[row * col] isa Int
                @test A[row * col] == 42i + row * col
                A[row, col] = 42i + row * col + 1
                @test A[row, col] isa Int
                @test A[row, col] == 42i + row * col + 1
            end
        end
        @test_throws BoundsError A[]
        @test_throws BoundsError A[0]
        @test_throws BoundsError A[0, 0]
        @test_throws BoundsError A[0, 1]
        @test_throws BoundsError A[1, 0]
        @test_throws BoundsError A[13]
        @test_throws BoundsError A[1, 7]
        @test_throws BoundsError A[3, 1]
        @test_throws BoundsError A[] = 42
        @test_throws BoundsError A[0] = 42
        @test_throws BoundsError A[0, 0] = 42
        @test_throws BoundsError A[0, 1] = 42
        @test_throws BoundsError A[1, 0] = 42
        @test_throws BoundsError A[13] = 42
        @test_throws BoundsError A[1, 7] = 42
        @test_throws BoundsError A[3, 1] = 42
    end

    @test_throws AssertionError BlockMatrix(1, 2, B11)
    @test_throws AssertionError BlockMatrix{Int}(1, 2, B11)
    @test_throws AssertionError BlockMatrix(1, 2, B11, B12, B12)
    @test_throws AssertionError BlockMatrix{Int}(1, 2, B11, B12, B12)
    @test_throws MethodError BlockMatrix{Float64}(1, 2, B11, B12)
end

@testset "single block col" begin
    B11 = [1 2 3; 4 5 6]
    B21 = [7 8 9; 10 11 12]
    B = Array{AbstractArray{Int, 2}, 2}(undef, 2, 1)
    B[1] = B11
    B[2] = B21

    for (i, A) in enumerate([
        BlockMatrix(B),
        BlockMatrix{Int}(B),
        BlockMatrix(2, 1, B11, B21),
        BlockMatrix{Int}(2, 1, B11, B21)
    ])
        @test A isa AbstractArray{Int, 2}
        @test size(A) == (4, 3)
        @test length(A) == 12
        for row in 1:4
            for col in 1:3
                A[row * col] = 42i + row * col
                @test A[row * col] isa Int
                @test A[row * col] == 42i + row * col
                A[row, col] = 42i + row * col + 1
                @test A[row, col] isa Int
                @test A[row, col] == 42i + row * col + 1
            end
        end
        @test_throws BoundsError A[]
        @test_throws BoundsError A[0]
        @test_throws BoundsError A[0, 0]
        @test_throws BoundsError A[0, 1]
        @test_throws BoundsError A[1, 0]
        @test_throws BoundsError A[13]
        @test_throws BoundsError A[1, 4]
        @test_throws BoundsError A[5, 1]
        @test_throws BoundsError A[] = 42
        @test_throws BoundsError A[0] = 42
        @test_throws BoundsError A[0, 0] = 42
        @test_throws BoundsError A[0, 1] = 42
        @test_throws BoundsError A[1, 0] = 42
        @test_throws BoundsError A[13] = 42
        @test_throws BoundsError A[1, 4] = 42
        @test_throws BoundsError A[5, 1] = 42
    end

    @test_throws AssertionError BlockMatrix(2, 1, B11)
    @test_throws AssertionError BlockMatrix{Int}(2, 1, B11)
    @test_throws AssertionError BlockMatrix(2, 1, B11, B21, B21)
    @test_throws AssertionError BlockMatrix{Int}(2, 1, B11, B21, B21)
    @test_throws MethodError BlockMatrix{Float64}(2, 1, B11, B21)
end

@testset "ordinary" begin
    B11 = [1 2 3; 7 8 9]
    B12 = [4 5 6; 10 11 12]
    B21 = [13 14 15; 19 20 21]
    B22 = [16 17 18; 22 23 24]
    B = Array{AbstractArray{Int, 2}, 2}(undef, 2, 2)
    B[1] = B11
    B[2] = B21
    B[3] = B12
    B[4] = B22

    for (i, A) in enumerate([
        BlockMatrix(B),
        BlockMatrix{Int}(B),
        BlockMatrix(2, 2, B11, B12, B21, B22),
        BlockMatrix{Int}(2, 2, B11, B12, B21, B22)
    ])
        @test A isa AbstractArray{Int, 2}
        @test size(A) == (4, 6)
        @test length(A) == 24
        for row in 1:4
            for col in 1:6
                A[row * col] = 42i + row * col
                @test A[row * col] isa Int
                @test A[row * col] == 42i + row * col
                A[row, col] = 42i + row * col + 1
                @test A[row, col] isa Int
                @test A[row, col] == 42i + row * col + 1
            end
        end
        @test_throws BoundsError A[]
        @test_throws BoundsError A[0]
        @test_throws BoundsError A[0, 0]
        @test_throws BoundsError A[0, 1]
        @test_throws BoundsError A[1, 0]
        @test_throws BoundsError A[25]
        @test_throws BoundsError A[1, 7]
        @test_throws BoundsError A[5, 1]
        @test_throws BoundsError A[] = 42
        @test_throws BoundsError A[0] = 42
        @test_throws BoundsError A[0, 0] = 42
        @test_throws BoundsError A[0, 1] = 42
        @test_throws BoundsError A[1, 0] = 42
        @test_throws BoundsError A[25] = 42
        @test_throws BoundsError A[1, 7] = 42
        @test_throws BoundsError A[5, 1] = 42
    end

    @test_throws AssertionError BlockMatrix(2, 2, B11, B12, B21)
    @test_throws AssertionError BlockMatrix{Int}(2, 2, B11, B12, B21)
    @test_throws AssertionError BlockMatrix(2, 2, B11, B12, B21, B22, B22)
    @test_throws AssertionError BlockMatrix{Int}(2, 2, B11, B12, B21, B22, B22)
    @test_throws MethodError BlockMatrix{Float64}(2, 2, B11, B12, B21, B22)
end

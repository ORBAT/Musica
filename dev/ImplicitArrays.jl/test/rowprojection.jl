@testset "invalid row bounds" begin
    v = [1, 2, 3]
    @test_throws BoundsError RowProjectionVector(v, 0)
    @test_throws BoundsError RowProjectionVector(v, 4)

    M = [1 2 3; 4 5 6; 7 8 9]
    @test_throws BoundsError RowProjectionMatrix(M, 0)
    @test_throws BoundsError RowProjectionMatrix(M, 0, 1)
    @test_throws BoundsError RowProjectionMatrix(M, 1, 0)
    @test_throws BoundsError RowProjectionMatrix(M, 4)
    @test_throws BoundsError RowProjectionMatrix(M, 1, 4)
    @test_throws BoundsError RowProjectionMatrix(M, 4, 1)
end

@testset "single row" begin
    v = [1, 2, 3]
    for row ∈ 1:length(v)
        u = RowProjectionVector(v, row)
        @test u isa RowProjectionVector{Int}
        @test size(u) == (1,)
        @test length(u) == 1
        @test_throws BoundsError u[0]
        @test_throws BoundsError u[0] = 41
        @test u[] == v[row]
        @test u[1] == v[row]
        u[] = 10 + row
        @test u[] == 10 + row
        u[1] = 100 + row
        @test u[1] == 100 + row
        @test_throws BoundsError u[length(u) + 1]
        @test_throws BoundsError u[length(u) + 1] = 41
    end

    M = [1 2 3; 4 5 6; 7 8 9]
    for row ∈ 1:size(M, 1)
        A = RowProjectionMatrix(M, row)
        @test A isa RowProjectionMatrix{Int}
        @test size(A) == (1, size(M, 2))
        @test length(A) == size(M, 1)
        @test_throws BoundsError A[]
        @test_throws BoundsError A[] = 41
        @test_throws BoundsError A[0]
        @test_throws BoundsError A[0] = 41
        for col ∈ 1:size(M, 2)
            @test A[col] == M[row, col]
            @test A[1, col] == M[row, col]

            A[col] = row + col
            @test A[col] == row + col
            @test A[1, col] == row + col
            @test M[row, col] == row + col

            A[1, col] = 10 + row + col
            @test A[col] == 10 + row + col
            @test A[1, col] == 10 + row + col
            @test M[row, col] == 10 + row + col

            M[row, col] = 100 + row + col
            @test A[col] == 100 + row + col
            @test A[1, col] == 100 + row + col
        end
        @test_throws BoundsError A[length(A) + 1]
        @test_throws BoundsError A[length(A) + 1] = 41
    end
end

@testset "row subset" begin
    v = [1, 2, 3]
    u = RowProjectionVector(v, 3, 1)
    @test u isa RowProjectionVector{Int}
    @test size(u) == (2,)
    @test length(u) == 2
    @test_throws BoundsError u[0]
    @test_throws BoundsError u[0] = 41
    @test u[1] == v[3]
    u[1] = 11
    @test u[1] == v[3] == 11
    @test u[2] == v[1]
    u[2] = 12
    @test u[2] == v[1] == 12
    @test_throws BoundsError u[length(u) + 1]
    @test_throws BoundsError u[length(u) + 1] = 41

    M = [1 2 3; 4 5 6; 7 8 9]
    A = RowProjectionMatrix(M, 3, 1)
    @test A isa RowProjectionMatrix{Int}
    @test size(A) == (2, size(M, 2))
    @test length(A) == 2 * size(M, 2)
    @test_throws BoundsError A[]
    @test_throws BoundsError A[] = 41
    @test_throws BoundsError A[0]
    @test_throws BoundsError A[0] = 41
    @test A[1, :] == M[3, :]
    A[1, :] .= [11, 12, 13]
    @test A[1, :] == M[3, :] == [11, 12, 13]
    @test A[2, :] == M[1, :]
    A[2, :] .= [21, 22, 23]
    @test A[2, :] == M[1, :] == [21, 22, 23]
    @test_throws BoundsError A[length(A) + 1]
    @test_throws BoundsError A[length(A) + 1] = 41
end

@testset "row bag" begin
    v = [1, 2, 3]
    u = RowProjectionVector(v, 2, 2)
    @test u isa RowProjectionVector{Int}
    @test size(u) == (2,)
    @test length(u) == 2
    @test_throws BoundsError u[0]
    @test_throws BoundsError u[0] = 41
    @test u[1] == u[2] == v[2]
    u[1] = 11
    @test u[1] == u[2] == v[2] == 11
    u[2] = 12
    @test u[1] == u[2] == v[2] == 12
    @test_throws BoundsError u[length(u) + 1]
    @test_throws BoundsError u[length(u) + 1] = 41

    M = [1 2 3; 4 5 6; 7 8 9]
    A = RowProjectionMatrix(M, 2, 2)
    @test A isa RowProjectionMatrix{Int}
    @test size(A) == (2, size(M, 2))
    @test length(A) == 2 * size(M, 2)
    @test_throws BoundsError A[]
    @test_throws BoundsError A[] = 41
    @test_throws BoundsError A[0]
    @test_throws BoundsError A[0] = 41
    @test A[1, :] == A[2, :] == M[2, :]
    A[1, :] .= [11, 12, 13]
    @test A[1, :] == A[2, :] == M[2, :] == [11, 12, 13]
    A[2, :] .= [21, 22, 23]
    @test A[1, :] == A[2, :] == M[2, :] == [21, 22, 23]
    @test_throws BoundsError A[length(A) + 1]
    @test_throws BoundsError A[length(A) + 1] = 41
end

@testset "full projection" begin
    v = [1, 2, 3]
    u = RowProjectionVector(v, 1, 2, 3)
    @test u isa RowProjectionVector{Int}
    @test size(u) == size(v)
    @test length(u) == length(v)
    @test_throws BoundsError u[0]
    @test_throws BoundsError u[0] = 41
    @test u == v
    for row in 1:length(v)
        u[row] = 10 + row
        @test u[row] == 10 + row
        @test v[row] == 10 + row
    end
    @test u == v
    @test_throws BoundsError u[length(u) + 1]
    @test_throws BoundsError u[length(u) + 1] = 41

    M = [1 2 3; 4 5 6; 7 8 9]
    A = RowProjectionMatrix(M, 1, 2, 3)
    @test A isa RowProjectionMatrix{Int}
    @test size(A) == size(M)
    @test length(A) == length(M)
    @test_throws BoundsError A[]
    @test_throws BoundsError A[] = 41
    @test_throws BoundsError A[0]
    @test_throws BoundsError A[0] = 41
    @test A == M
    for row ∈ 1:size(M, 1)
        for col ∈ 1:size(M, 2)
            @test A[row, col] == M[row, col]

            A[row, col] = 10 + row + col
            @test A[row, col] == 10 + row + col
            @test M[row, col] == 10 + row + col
        end
    end
    @test_throws BoundsError A[length(A) + 1]
    @test_throws BoundsError A[length(A) + 1] = 41
end

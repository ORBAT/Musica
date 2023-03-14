"""
    BlockMatrix{T} <: AbstractArray{T, 2}

Implicit block matrix of equally-sized matrices with elements of type `T`.

# Constructors
    BlockMatrix(blocks)
    BlockMatrix{T}(blocks)
    BlockMatrix{T}(rows, cols[, blocks...])
    BlockMatrix(rows, cols, first_block[, more_blocks...])

Create a new block matrix from the given matrix of matrices. Alternatively, create the
block matrix from a sequence of matrices, given the number of `rows` and `cols`.

# Examples

```jldoctest; setup = :(using ImplicitArrays)
julia> A = [1 2; 3 4]; B = zeros(Int, 2, 2);

julia> C = [x * y for x in 2:3, y in 3:4];

julia> BlockMatrix(1, 4, A, B, B, C)
2×8 BlockMatrix{Int64}:
 1  2  0  0  0  0  6   8
 3  4  0  0  0  0  9  12
```

!!! note
    This type is not suitable for high-performance purposes, as matrix blocks are
    stored in an abstract container to allow the composition of arbitrary matrix types.
    For more details, please refer to the
    [performance tips](https://docs.julialang.org/en/v1/manual/performance-tips/)
    in the official Julia documentation.
"""
struct BlockMatrix{T} <: AbstractArray{T, 2}
    "Dimensions of the (equally-sized) matrix blocks"
    bdims::NTuple{2, Int}
    "Matrix blocks"
    blocks::Array{AbstractArray{T, 2}, 2}

    function BlockMatrix{T}(
        blocks::Array{AbstractArray{T, 2}, 2}
    ) where T
        bdims = (1, 1)
        for (i, block) ∈ enumerate(blocks)
            i > 1 && @assert(
                size(block) == bdims,
                "invalid block dimensions (block $i expected $bdims, got $(size(block)))"
            )
            bdims = size(block)
        end
        new(bdims, blocks)
    end
end

@inline BlockMatrix(
    blocks::Array{AbstractArray{T, 2}, 2}
) where T = BlockMatrix{T}(blocks)

function BlockMatrix{T}(
    rows::Int,
    cols::Int,
    blocks::Vararg{AbstractArray{T, 2}}
) where T
    @assert(
        rows * cols == length(blocks),
        "invalid number of blocks given (expected $(rows * cols), got $(length(blocks)))"
    )
    B = Array{AbstractArray{T, 2}, 2}(undef, rows, cols)
    for (i, b) in enumerate(blocks)
        B[Int(ceil(i/cols)), (i - 1) % cols + 1] = b
    end
    BlockMatrix{T}(B)
end

@inline BlockMatrix(
    rows::Int,
    cols::Int,
    block::AbstractArray{T, 2},
    blocks::Vararg{AbstractArray{T, 2}}
) where T = BlockMatrix{T}(rows, cols, block, blocks...)

@inline Base.size(
    M::BlockMatrix{T}
) where T = M.bdims .* size(M.blocks)

@inline Base.getindex(
    M::BlockMatrix{T},
    I::Vararg{Int, 2}
) where T = Base.getindex(
    M.blocks[Int(ceil(I[1]/M.bdims[1])), Int(ceil(I[2]/M.bdims[2]))],
    (I[1] - 1) % M.bdims[1] + 1,
    (I[2] - 1) % M.bdims[2] + 1
)

@inline Base.setindex!(
    M::BlockMatrix{T},
    v::Any,
    I::Vararg{Int, 2}
) where T = Base.setindex!(
    M.blocks[Int(ceil(I[1]/M.bdims[1])), Int(ceil(I[2]/M.bdims[2]))],
    v,
    (I[1] - 1) % M.bdims[1] + 1,
    (I[2] - 1) % M.bdims[2] + 1
)

```@meta
    CurrentModule = ImplicitArrays
```
# ImplicitArrays.jl

The `ImplicitArrays.jl` package provides multiple implicit array types for the [Julia](https://julialang.org) programming language. In many situations, the implicit array types can be used as drop-in replacements for regular Julia arrays, while carrying a smaller memory footprints as their explicit counterparts.


## Block matrices

This section presents a [block matrix](https://en.wikipedia.org/wiki/Block_matrix) type for equally-sized blocks (sharing a common element type). The `BlockMatrix` type can be used to encapsulate and mix different matrix blocks, e.g., regular matrices and implicit matrices at the same time.

```@docs
    BlockMatrix
```


## Fixed-value arrays

Fixed-value arrays "replicate" a single value across arbitrary array dimensions. The resulting arrays have a constant memory footprint (i.e., the represented value and the array dimensions) and can only be read from.

```@docs
    FixedValueArray
```


## Interaction matrices

An interaction matrix `M` of size `n × m` consist of a list of `n` elements `rᵢ ∈ R` (*row elements*), a list of `m` elements `cⱼ ∈ C` (*column elements*), and a *interaction function* `f: R × C → T`, such that each element `Mᵢⱼ` of the matrix can be computed as `f(rᵢ, cⱼ)`.

### Interaction functions
```@docs
    InteractionFunction
    ConstInteractionFunction
    GenericInteractionFunction
```

### Interaction matrices
```@docs
    InteractionMatrix
```


## Row-projection arrays

Row-projection arrays represent views on existing vectors or matrices, where the projections are created from a sequence of valid row indices corresponding to the vector or matrix. Row indices can occur multiple times and at arbitrary positions in the sequence.

```@docs
    RowProjectionVector
    RowProjectionMatrix
```

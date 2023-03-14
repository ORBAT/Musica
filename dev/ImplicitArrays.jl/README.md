# Implicit arrays for Julia
[![](https://img.shields.io/github/actions/workflow/status/tkemmer/ImplicitArrays.jl/CI.yml?branch=master&style=for-the-badge)](https://github.com/tkemmer/ImplicitArrays.jl/actions/workflows/CI.yml)
[![](https://img.shields.io/github/license/tkemmer/ImplicitArrays.jl?style=for-the-badge)](https://github.com/tkemmer/ImplicitArrays.jl/blob/master/LICENSE)
[![](https://img.shields.io/badge/docs-stable-blue.svg?style=for-the-badge)](https://tkemmer.github.io/ImplicitArrays.jl/stable)
[![](https://img.shields.io/badge/docs-dev-blue.svg?style=for-the-badge)](https://tkemmer.github.io/ImplicitArrays.jl/dev)


The `ImplicitArrays.jl` package provides multiple implicit array types for the [Julia](https://julialang.org) programming language.

## Implicit array types
A full list of implicit array types provided by this package (along with code examples) is available in the [documentation](https://tkemmer.github.io/ImplicitArrays.jl/dev).

## Installation
This package version requires Julia 1.6 or above. In the Julia shell, switch to the
`Pkg` shell by pressing `]` and enter the following command:

```sh
pkg> add ImplicitArrays
```

## Testing
`ImplicitArrays.jl` provides tests for most of its functions. You can run the test suite with the
following command in the `Pkg` shell:
```sh
pkg> test ImplicitArrays
```

## Citing
If you use `ImplicitArrays.jl` in your research, please cite the following publication:
> Kemmer, T (2021). Space-efficient and exact system representations for the nonlocal protein
> electrostatics problem. Ph. D. thesis, Johannes Gutenberg University Mainz. Mainz, Germany.

Citation items for BibTeX can be found in [CITATION.bib](https://github.com/tkemmer/ImplicitArrays.jl/blob/master/CITATION.bib).

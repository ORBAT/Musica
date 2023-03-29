"""
```jldoctest
Musica.fuck + 1

# output

2
```
"""
module Musica
const fuck = 1
export fuck

include("CA.jl")
export CA
end


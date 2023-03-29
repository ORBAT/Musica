using Test
using Documenter
using Musica

@test CA.rule_to_ruleset(30) == [0, 1, 1, 1, 1, 0, 0, 0]
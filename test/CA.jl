using Test
using Documenter
using Musica


@test_throws AssertionError CA.rule_to_ruleset(256)
@test_throws AssertionError CA.rule_to_ruleset(-1)
@test_throws AssertionError CA.rule_to_ruleset(3^27, 3)
@test CA.rule_to_ruleset(22, 3) == [[1, 1, 2]; zeros(Int, 27 - 3)]
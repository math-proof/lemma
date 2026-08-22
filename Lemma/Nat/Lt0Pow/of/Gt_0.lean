import sympy.Basic


@[main]
private lemma main
  [MonoidWithZero M₀]
  [PartialOrder M₀]
  [PosMulStrictMono M₀]
  [ZeroLEOneClass M₀]
  {x : M₀}
  {n : ℕ}
-- given
  (h_x : x > 0) :
-- imply
  x ^ n > 0 :=
-- proof
  pow_pos h_x n


-- created on 2023-04-15
-- updated on 2026-08-22

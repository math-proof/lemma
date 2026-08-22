import sympy.Basic


@[main]
private lemma main
  [GroupWithZero G₀]
  [PartialOrder G₀]
  [PosMulReflectLT G₀]
  [ZeroLEOneClass G₀]
  {x : G₀}
  {n : ℤ}
-- given
  (h_x : x > 0) :
-- imply
  x ^ n > 0 :=
-- proof
  zpow_pos h_x n


-- created on 2023-04-15
-- updated on 2026-08-22

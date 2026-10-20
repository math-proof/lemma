import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n b : ℤ}
-- given
  (h₀ : n ≤ b) :
-- imply
  n ∈ Set.Iic b :=
-- proof
  Set.mem_Iic.mpr h₀


-- created on 2021-05-21
-- updated on 2026-10-17

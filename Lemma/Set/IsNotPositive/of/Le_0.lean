import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
-- given
  (h₀ : x ≤ 0) :
-- imply
  x ∈ Set.Iic 0 :=
-- proof
  Set.mem_Iic.mpr h₀


-- created on 2026-10-11
-- updated on 2026-10-17

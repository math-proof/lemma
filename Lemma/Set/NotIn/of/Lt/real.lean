import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n a : ℝ}
-- given
  (h₀ : n ∉ Set.Ici a) :
-- imply
  n < a := by
-- proof
  simpa [Set.mem_Ici] using h₀


-- created on 2021-09-05
-- updated on 2026-10-17

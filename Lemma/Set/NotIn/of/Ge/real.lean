import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n a : ℝ}
-- given
  (h₀ : n ∉ Set.Iio a) :
-- imply
  n ≥ a := by
-- proof
  simpa [Set.mem_Iio] using h₀


-- created on 2026-10-11
-- updated on 2026-10-17

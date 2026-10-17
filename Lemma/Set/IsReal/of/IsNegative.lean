import sympy.functions.elementary.complexes
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
-- given
  (h₀ : x ∈ Set.Iio 0) :
-- imply
  (x : ℂ) ∈ Set.range Complex.ofReal ∧ (x : ℂ).re < 0 := by
-- proof
  refine ⟨⟨x, rfl⟩, ?_⟩
  simpa [Complex.ofReal_re, Set.mem_Iio] using h₀


-- created on 2026-10-11
-- updated on 2026-10-17

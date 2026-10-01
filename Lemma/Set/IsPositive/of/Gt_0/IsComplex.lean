import sympy.functions.elementary.complexes
import sympy.Basic
open scoped ComplexOrder


@[main]
private lemma main
  {x : ℂ}
-- given
  (h₀ : x > 0)
  (_h₁ : x ∈ (Set.univ : Set ℂ)) :
-- imply
  x ∈ Complex.ofReal '' Set.Ioi 0 := by
-- proof
  obtain ⟨h_re, h_im⟩ := Complex.lt_def.mp h₀
  exact ⟨x.re, h_re, Complex.ext (by simp) (by simpa using h_im)⟩


-- created on 2026-09-27

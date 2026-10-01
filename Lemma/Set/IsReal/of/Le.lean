import sympy.functions.elementary.complexes
import sympy.Basic
open scoped ComplexOrder


@[main]
private lemma main
  {x : ℂ}
  {b : ℝ}
-- given
  (h : x ≤ b) :
-- imply
  x ∈ Set.range Complex.ofReal := by
-- proof
  have h_im := (Complex.le_def.mp h).2
  rw [Complex.ofReal_im] at h_im
  exact ⟨x.re, Complex.ext (by simp) (by simp only [Complex.ofReal_im]; exact h_im.symm)⟩


-- created on 2021-02-15

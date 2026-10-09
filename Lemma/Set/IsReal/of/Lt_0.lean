import sympy.functions.elementary.complexes
import sympy.Basic
open scoped ComplexOrder


@[path]
private lemma main
  {x : ℂ}
-- given
  (h : x < 0) :
-- imply
  x ∈ Set.range Complex.ofReal := by
-- proof
  have h_im := (Complex.lt_def.mp h).2
  rw [Complex.zero_im] at h_im
  exact ⟨x.re, Complex.ext (by simp) (by simp only [Complex.ofReal_im]; exact h_im.symm)⟩


-- created on 2021-06-04

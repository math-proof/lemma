import sympy.functions.elementary.complexes
import sympy.Basic
open scoped ComplexOrder


@[path]
private lemma main
  {x : ℂ}
  {y : ℝ}
-- given
  (h : x ≤ y) :
-- imply
  ~x = x := by
-- proof
  have h_im := (Complex.le_def.mp h).2
  rw [Complex.ofReal_im] at h_im
  exact Complex.conj_eq_iff_im.mpr h_im


-- created on 2023-05-01

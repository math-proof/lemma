import sympy.functions.elementary.complexes
import sympy.functions.elementary.trigonometric
import Lemma.Complex.ExpMulI.eq.AddCos_MulISin
open Complex


@[main]
private lemma main
-- given
  (x : ℝ) :
-- imply
  (I * x).exp = x.cos + I * x.sin := by
-- proof
  have h_cos : x.cos = (x : ℂ).cos := by simp
  have h_sin : x.sin = (x : ℂ).sin := by simp
  rw [h_cos, h_sin]
  apply ExpMulI.eq.AddCos_MulISin


-- created on 2025-01-05
-- updated on 2025-10-07

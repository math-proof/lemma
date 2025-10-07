import sympy.functions.elementary.trigonometric
import sympy.functions.elementary.complexes
import Lemma.Algebra.EqMulS.of.Eq
import Lemma.Algebra.Mul
open Algebra


@[main]
private lemma main
  {z : ℂ} :
-- imply
  im z = ‖z‖ * sin (arg z) := by
-- proof
  have h := Complex.sin_arg z
  have h := EqMulS.of.Eq h ‖z‖
  by_cases h_Ne_0 : z ≠ 0
  simp [h_Ne_0] at h
  rw [Mul.comm] at h
  exact h.symm
  simp


-- created on 2025-01-13

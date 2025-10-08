import sympy.functions.elementary.trigonometric
import Lemma.Algebra.Expr.eq.AddRe_MulIIm
import Lemma.Algebra.EqMulS.of.Eq
import Lemma.Nat.Mul
open Algebra Nat


@[main]
private lemma main
  {z : ℂ} :
-- imply
  re z = ‖z‖ * cos (arg z) := by
-- proof
  by_cases h_Ne_0 : z ≠ 0
  have h := Complex.cos_arg h_Ne_0
  have h := EqMulS.of.Eq h ‖z‖
  simp [h_Ne_0] at h
  rw [Mul.comm] at h
  exact h.symm
  simp


-- created on 2025-01-13

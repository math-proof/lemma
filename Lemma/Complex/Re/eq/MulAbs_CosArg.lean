import sympy.functions.elementary.trigonometric
import Lemma.Complex.Expr.eq.AddRe_MulIIm
import Lemma.Nat.EqMulS.of.Eq
import Lemma.Nat.Mul
open Nat Complex


@[main]
private lemma main
  {z : ℂ} :
-- imply
  re z = ‖z‖ * (arg z).cos := by
-- proof
  by_cases h_Ne_0 : z ≠ 0
  have h := Complex.cos_arg h_Ne_0
  have h := EqMulS.of.Eq h ‖z‖
  simp [h_Ne_0] at h
  rw [Mul.comm] at h
  exact h.symm
  simp


-- created on 2025-01-13

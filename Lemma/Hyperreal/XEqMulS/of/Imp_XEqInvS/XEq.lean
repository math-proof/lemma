import Lemma.Hyperreal.XEqMulS.of.XEq.Imp_XEqInvS
open Hyperreal


@[main]
private lemma main
  {a b x : ℝ*}
-- given
  (h_xinfty : (x → ∞) → a⁻¹ ≈ b⁻¹)
  (h : a ≈ b) :
-- imply
  x * a ≈ x * b := by
-- proof
  rw [mul_comm]
  conv_rhs =>
    rw [mul_comm]
  exact XEqMulS.of.XEq.Imp_XEqInvS h h_xinfty


-- created on 2026-07-30

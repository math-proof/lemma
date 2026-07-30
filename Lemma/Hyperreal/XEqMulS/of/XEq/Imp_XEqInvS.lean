import Lemma.Hyperreal.XEqMulS.of.XEq.XEq.Imp_XEqInvS.Imp_XEqInvS
open Hyperreal


@[main]
private lemma main
  {a b x : ℝ*}
-- given
  (h : a ≈ b)
  (h_xinfty : (x → ∞) → a⁻¹ ≈ b⁻¹) :
-- imply
  a * x ≈ b * x :=
-- proof
  XEqMulS.of.XEq.XEq.Imp_XEqInvS.Imp_XEqInvS h_xinfty (by aesop) h (Setoid.refl _)


-- created on 2026-07-29

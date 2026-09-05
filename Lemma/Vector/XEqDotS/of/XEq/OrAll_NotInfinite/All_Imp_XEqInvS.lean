import Lemma.Hyperreal.XEqMulS.of.XEq.Imp_XEqInvS
import Lemma.Nat.Mul
import Lemma.Vector.Dot
import Lemma.Vector.XEqSumS.of.XEq.OrAll_NotInfinite
open Hyperreal Vector Nat


@[main]
private lemma main
  {a b c : List.Vector ℝ* n}
-- given
  (h_xinfty : ∀ i : Fin n, (c[i] → ∞) → a[i]⁻¹ ≈ b[i]⁻¹)
  (h_or : (∀ i : Fin n, ¬((b * c)[i] → ∞)) ∨ b * c ≥ 0 ∨ b * c ≤ 0)
  (h : a ≈ b) :
-- imply
  a @ c ≈ b @ c := by
-- proof
  rw [Dot.eq.SumMul, Dot.eq.SumMul]
  apply XEqSumS.of.XEq.OrAll_NotInfinite h_or
  refine Vector.XEq.of.All_XEqGetS.fin ?_
  intro i
  rw [GetMul.eq.MulGetS.fin a c i, GetMul.eq.MulGetS.fin b c i]
  exact XEqMulS.of.XEq.Imp_XEqInvS (All_XEqGetS.of.XEq.fin h i) (h_xinfty i)


@[main]
private lemma left
  {a b c : List.Vector ℝ* n}
-- given
  (h_xinfty : ∀ i : Fin n, (c[i] → ∞) → a[i]⁻¹ ≈ b[i]⁻¹)
  (h_or : (∀ i : Fin n, ¬((c * b)[i] → ∞)) ∨ c * b ≥ 0 ∨ c * b ≤ 0)
  (h : a ≈ b) :
-- imply
  c @ a ≈ c @ b := by
-- proof
  rw [Dot.comm]
  conv_rhs => rw [Dot.comm]
  rw [Mul.comm] at h_or
  apply main h_xinfty h_or h


-- created on 2026-07-29
-- updated on 2026-09-05

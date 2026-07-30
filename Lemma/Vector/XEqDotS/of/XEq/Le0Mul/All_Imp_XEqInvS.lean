import Lemma.Hyperreal.XEqMulS.of.XEq.Imp_XEqInvS
import Lemma.Nat.Mul
import Lemma.Vector.Dot
import Lemma.Vector.XEqSumS.of.XEq.Ge_0
open Hyperreal Vector Nat


@[main]
private lemma main
  {a b x : List.Vector ℝ* n}
-- given
  (h_xinfty : ∀ i : Fin n, (x[i] → ∞) → a[i]⁻¹ ≈ b[i]⁻¹)
  (h_pos : b * x ≥ 0)
  (h : a ≈ b) :
-- imply
  a @ x ≈ b @ x := by
-- proof
  rw [Dot.eq.SumMul, Dot.eq.SumMul]
  apply XEqSumS.of.XEq.Ge_0 h_pos
  refine Vector.XEq.of.All_XEqGetS.fin ?_
  intro i
  rw [GetMul.eq.MulGetS.fin a x i, GetMul.eq.MulGetS.fin b x i]
  exact XEqMulS.of.XEq.Imp_XEqInvS (All_XEqGetS.of.XEq.fin h i) (h_xinfty i)


@[main]
private lemma left
  {a b x : List.Vector ℝ* n}
-- given
  (h_xinfty : ∀ i : Fin n, (x[i] → ∞) → a[i]⁻¹ ≈ b[i]⁻¹)
  (h_pos : x * b ≥ 0)
  (h : a ≈ b) :
-- imply
  x @ a ≈ x @ b := by
-- proof
  rw [Dot.comm]
  conv_rhs => rw [Dot.comm]
  apply main h_xinfty _ h
  rwa [← Mul.comm x b]


-- created on 2026-07-29

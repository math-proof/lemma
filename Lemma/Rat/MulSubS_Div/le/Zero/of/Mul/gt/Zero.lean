import sympy.core.relational
import Lemma.Algebra.MulAdd.eq.AddMulS
import Lemma.Algebra.Mul_Add.eq.AddMulS
import Lemma.Algebra.EqMulS.of.Eq.Eq
import Lemma.Algebra.Sub.eq.NegSub
import Lemma.Algebra.DivMul.eq.Mul_Div
import Lemma.Algebra.EqSubS.is.Eq
import Lemma.Algebra.DivMul.eq.MulDiv
import Lemma.Algebra.SubDivS.eq.Div_Mul__SubMulS.of.Ne_0.Ne_0
import Lemma.Algebra.Mul_Neg.eq.NegSquare
import Lemma.Rat.DivDiv.eq.Div_Mul
import Lemma.Algebra.MulMul.eq.Mul_Mul
import Lemma.Algebra.MulMul
import Lemma.Algebra.GtMulS.of.Gt.Gt_0
import Lemma.Algebra.EqMul0_0
import Lemma.Algebra.LeNegSquare_0
import Lemma.Algebra.Add.ne.Zero.of.Mul.gt.Zero
import Lemma.Algebra.GtSquare_0.of.Ne_0
import Lemma.Algebra.LeDivS.of.Le.Gt_0
import Lemma.Algebra.Ne_0.of.Mul.gt.Zero
import Lemma.Algebra.Square.eq.Mul
open Algebra Rat


@[main]
private lemma main
  -- R is a linear ordered field, e.g. ℝ or ℚ
  [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  -- TP denotes true positives
  -- TN denotes true negatives
  -- P denotes positives
  -- N denotes negatives
  -- A denotes accuracy
  {TP TN P N : R}
-- given
  (h₀ : P * N > 0) :
-- imply
  let A := (TP + TN) / (P + N)
  (A - TP / P) * (A - TN / N) ≤ 0 := by
-- proof
  denote h_A : A = _
  have h_Add_ne_Zero := Add.ne.Zero.of.Mul.gt.Zero h₀
  have h₁ := EqSubS.of.Eq (TP / P) h_A
  have h_together := SubDivS.eq.Div_Mul__SubMulS.of.Ne_0.Ne_0
    h_Add_ne_Zero
    (Ne_0.of.Mul.gt.Zero.left h₀)
    (x := TP + TN)
    (y := TP)
  have h₁ := Eq.trans h₁ h_together
  rw [
    MulAdd.eq.AddMulS,
    Mul_Add.eq.AddMulS
  ] at h₁
  simp at h₁
  have h₂ := EqSubS.of.Eq (TN / N) h_A
  have h_together := SubDivS.eq.Div_Mul__SubMulS.of.Ne_0.Ne_0
    h_Add_ne_Zero
    (Ne_0.of.Mul.gt.Zero h₀)
    (x := TP + TN)
    (y := TN)
  have h₂ := Eq.trans h₂ h_together
  rw [
    MulAdd.eq.AddMulS,
    Mul_Add.eq.AddMulS
  ] at h₂
  simp at h₂
  rw [Sub.eq.NegSub (a := TP * N)] at h₂
  have h := EqMulS.of.Eq.Eq h₁ h₂
  rw [Mul_Div.eq.DivMul] at h
  rw [MulDiv.eq.DivMul] at h
  rw [Mul_Neg.eq.NegSquare] at h
  rw [DivDiv.eq.Div_Mul] at h
  rw [Mul_Mul.eq.MulMul] at h
  rw [MulMul.comm (a := P + N)] at h
  rw [Mul.eq.Square] at h
  rw [MulMul.eq.Mul_Mul] at h
  have h_gt_0 := GtMulS.of.Gt.Gt_0 (GtSquare_0.of.Ne_0 h_Add_ne_Zero) h₀
  simp only [EqMul0_0] at h_gt_0
  have h_le_0 := LeNegSquare_0 (a := TN * P - TP * N)
  have h_le_0 := LeDivS.of.Le.Gt_0 h_le_0 h_gt_0
  simp at h_le_0
  rwa [← h] at h_le_0


-- created on 2024-11-29
-- updated on 2025-06-13

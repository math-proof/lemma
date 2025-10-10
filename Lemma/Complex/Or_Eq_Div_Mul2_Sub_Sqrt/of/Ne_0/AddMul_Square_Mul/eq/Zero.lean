import sympy.core.relational
import sympy.polys.polyroots
import Lemma.Algebra.SquareSub.eq.SubAddSquareS_MulMul2
import Lemma.Algebra.Mul_Sub.eq.SubMulS
import Lemma.Int.Eq_Neg.of.Add.eq.Zero
import Lemma.Algebra.SubAdd.eq.Add_Sub
import Lemma.Algebra.DivMul.eq.Mul_Div
import Lemma.Algebra.Square.eq.Mul
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Nat.Mul
import Lemma.Algebra.DivMul.eq.MulDiv
import Lemma.Algebra.SquareDiv.eq.DivSquareS
import Lemma.Algebra.SquareMul.eq.MulSquareS
import Lemma.Algebra.Eq_Inv_Div_Square.of.Ne_0
import Lemma.Algebra.Div.eq.Mul_Inv
import Lemma.Algebra.Eq_Mul_Div_Mul__Sub__SubDivS.of.Ne_0.Ne_0
import Lemma.Algebra.DivNeg.eq.NegDiv
import Lemma.Algebra.EqSub.is.Eq_Add
import Lemma.Algebra.DivAdd.eq.AddDivS
import Lemma.Algebra.NegMul.eq.MulNeg
import Lemma.Algebra.Mul_Neg.eq.NegMul
import Lemma.Algebra.Sub.eq.Add_Neg
import Lemma.Algebra.Mul_Add.eq.AddMulS
import Lemma.Algebra.DivMul.eq.Mul_Div
import Lemma.Rat.DivDiv.eq.Div_Mul
import Lemma.Algebra.MulSub.eq.SubMulS
import Lemma.Algebra.Div_Mul.eq.Inv.of.Ne_0
open Algebra Rat Int Nat


@[main]
private lemma main
  {x a b c : ℂ}
-- given
  (h₀ : a ≠ 0)
  (h₁ : a * x² + b * x + c = 0) :
-- imply
  let Δ : ℂ := b² - 4 * a * c
  x = (-b + √Δ) / (2 * a) ∨
    x = (-b - √Δ) / (2 * a) := by
-- proof
  let x' := x + b / (2 * a)
  have h₂ : x = x' - b / (2 * a) := by simp [x']
  rw [h₂] at h₁
  rw [
    SquareSub.eq.SubAddSquareS_MulMul2,
    Mul_Sub.eq.SubMulS,
    Mul_Add.eq.AddMulS,
    Mul_Sub.eq.SubMulS
  ] at h₁
  have h₁ := Eq_Neg.of.Add.eq.Zero h₁
  rw [Add_Sub.eq.SubAdd] at h₁
  rw [Mul_Div.eq.DivMul] at h₁
  rw [Mul_Div.eq.DivMul] at h₁
  rw [Mul_Div.eq.DivMul] at h₁
  rw [Mul.eq.Square] at h₁
  rw [Mul_Mul.eq.MulMul] at h₁
  rw [Mul_Mul.eq.MulMul] at h₁
  rw [Mul.comm (a := a) (b := 2)] at h₁
  rw [DivMul.eq.MulDiv] at h₁
  have h₂ : 2 * a ≠ 0 := by simp [h₀]
  simp [h₂] at h₁
  rw [Mul.comm (b := b)] at h₁
  simp at h₁
  rw [SquareDiv.eq.DivSquareS] at h₁
  rw [Mul_Div.eq.DivMul] at h₁
  rw [Mul.comm (b := b²)] at h₁
  rw [SquareMul.eq.MulSquareS] at h₁
  rw [Div_Mul.eq.DivDiv] at h₁
  rw [DivMul.eq.MulDiv] at h₁
  rw [DivMul.eq.Mul_Div] at h₁
  rw [Eq_Inv_Div_Square.of.Ne_0] at h₁
  rw [(by norm_num : (2 : ℂ)² = 4)] at h₁
  rw [Mul_Inv.eq.Div] at h₁
  rw [DivDiv.eq.Div_Mul] at h₁
  rw [SubAdd.eq.Add_Sub] at h₁
  have h₃ : 4 * a ≠ 0 := by simp [h₀]
  rw [Eq_Mul_Div_Mul__Sub__SubDivS.of.Ne_0.Ne_0 h₃ h₂] at h₁
  rw [SubMulS.eq.MulSub] at h₁
  rw [(by norm_num : (2 : ℂ) - 4 = -2)] at h₁
  rw [MulNeg.eq.NegMul] at h₁
  rw [DivNeg.eq.NegDiv] at h₁
  rw [Mul_Neg.eq.NegMul] at h₁
  rw [Add_Neg.eq.Sub] at h₁
  rw [Div_Mul.eq.Inv.of.Ne_0 h₂ true] at h₁
  rw [Mul_Inv.eq.Div] at h₁
  have h₁ := Eq_Add.of.EqSub h₁
  denote h_Δ : Δ = _
  have h_Δ := Eq_Add.of.EqSub h_Δ.symm
  rw [h_Δ] at h₁
  rw [DivAdd.eq.AddDivS] at h₁
  simp [h₃] at h₁
  sorry
  sorry


-- created on 2024-07-01
-- updated on 2025-04-16

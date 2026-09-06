import sympy.core.logic
import Lemma.Nat.Div.of.Eq
import Lemma.Rat.SquareDiv.eq.DivSquareS
import Lemma.Nat.Le.of.Gt_0.LeMulS
import Lemma.Rat.EqMul_Div.of.Ne_0
import Lemma.Real.Square.le.MulMul4.of.All_Le0Add_Mul_Square.Ge_0
import Lemma.Finset.Sum_Square.ge.Zero
import Lemma.Finset.Le0Add_MulSquare_SumSquare
import Lemma.Nat.Mul
import Lemma.Nat.MulMul.eq.Mul_Mul
open Nat Finset Real Rat


/-- cauchy_schwarz -/
@[main]
private lemma main
  [DecidableEq ι]
  {a b : ι → ℝ} :
-- imply
  (∑ i ∈ s, a i * b i)² ≤ (∑ i ∈ s, (a i)²) * ∑ i ∈ s, (b i)² := by
-- proof
  denote hA : A = ∑ i ∈ s, (a i)²
  denote hB : B = 2 * ∑ i ∈ s, a i * b i
  have hB := Div.of.Eq hB 2
  norm_num at hB
  denote hC : C = ∑ i ∈ s, (b i)²
  rw [← hA, ← hC, ← hB]
  rw [SquareDiv.eq.DivSquareS]
  norm_num
  apply Le.of.Gt_0.LeMulS (by norm_num : (4 : ℝ) > 0)
  rw [Mul_Mul.eq.MulMul]
  rw [EqMul_Div.of.Ne_0 (by norm_num : (4 : ℝ) ≠ 0)]
  apply Square.le.MulMul4.of.All_Le0Add_Mul_Square.Ge_0
  ·
    apply Sum_Square.ge.Zero
  ·
    intro x
    have := Le0Add_MulSquare_SumSquare (s := s) (x := x) (a := a) (b := b)
    rw [← hA, ← hC, ← hB] at this
    rw [Mul.comm (a := 2)] at this
    rw [MulMul.eq.Mul_Mul] at this
    rw [EqMul_Div.of.Ne_0 (by norm_num : (2 : ℝ) ≠ 0)] at this
    rw [Mul.comm] at this
    rwa [Mul.comm (a := x²)] at this


-- created on 2025-06-06
-- updated on 2026-09-06

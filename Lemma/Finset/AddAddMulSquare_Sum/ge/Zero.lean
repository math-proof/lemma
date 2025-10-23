import Lemma.Finset.Sum_SquareAddMul.ge.Zero
import Lemma.Nat.SquareAdd.eq.AddAddSquareS_MulMul2
import Lemma.Finset.Sum_Add.eq.AddSumS
import Lemma.Nat.SquareMul.eq.MulSquareS
import Lemma.Finset.MulSum.eq.Sum_Mul
import Lemma.Nat.AddAdd
import Lemma.Nat.Mul
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Finset.Mul_Sum.eq.Sum_Mul
open Nat Finset


@[main]
private lemma main
  -- [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [DecidableEq ι]
  {x : ℝ}
  {a b : ι → ℝ} :
-- imply
  x² * ∑ i ∈ s, (a i)² + 2 * x * ∑ i ∈ s, a i * b i + ∑ i ∈ s, (b i)² ≥ 0 := by
-- proof
  have := Sum_SquareAddMul.ge.Zero (s := s) (x := x) (a := a) (b := b)
  simp [SquareAdd.eq.AddAddSquareS_MulMul2] at this
  rw [Sum_Add.eq.AddSumS] at this
  rw [Sum_Add.eq.AddSumS] at this
  simp only [SquareMul.eq.MulSquareS] at this
  rw [Sum_Mul.eq.MulSum] at this
  simp only [Mul.comm (b := x)] at this
  rw [AddAdd.comm] at this
  simp [Mul_Mul.eq.MulMul] at this
  simp [MulMul.eq.Mul_Mul (a := 2 * x)] at this
  rw [Sum_Mul.eq.Mul_Sum] at this
  simp only [Mul.comm (b := x²)] at this
  assumption


-- created on 2025-04-06

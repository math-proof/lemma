import sympy.sets.sets
import Lemma.Bool.All.of.All.All_Imp
import Lemma.Algebra.Root_Add_2.le.Sqrt.of.Ge_1
import Lemma.Finset.LeSumS.of.All_Le
import Lemma.Real.Sum_Sqrt.le.SqrtMul_Sum.of.All_Ge_0
import Lemma.Algebra.Le.of.Le.Le
import Lemma.Nat.EqMulS.of.Eq
import Lemma.Rat.EqMulDiv.of.Ne_0
import Lemma.Nat.Mul_Mul
import Lemma.Algebra.Square.eq.Mul
import Lemma.Nat.Mul
import Lemma.Finset.Sum.ge.Zero.of.All_Ge_0
import Lemma.Rat.GeDivS.of.Ge.Gt_0
import Lemma.Nat.Gt_0.of.Ne_0
import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Real.EqSquareSqrt.of.Ge_0
import Lemma.Algebra.SqrtMulSquareS.eq.Mul.of.Ge_0.Ge_0
import Lemma.Real.GeSqrt_0
open Algebra Finset Bool Nat Real Rat


@[main]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ}
-- given
  (h₀ : n ≠ 0)
  (h₁ : ∀ i ∈ range n, x i ≥ 1)
  (h₂ : (∑ i ∈ range n, x i) / n = x n) :
-- imply
  (∑ i ∈ range n, (x i) ^ (1 / (i + 2) : ℝ)) ≤ n * √(x n) := by
-- proof
  have : ∀ (t : ℝ) (i : ℕ), t ≥ 1 → (t ^ (1 / (i + 2) : ℝ) ≤ √t) := by
    intro t i h
    apply Root_Add_2.le.Sqrt.of.Ge_1 h
  have := All.of.All.All_Imp.binary this h₁
  have h_Le := LeSumS.of.All_Le this
  have : ∀ t : ℝ, t ≥ 1 → t ≥ 0 := by
    intro t h
    linarith
  have h_Ge_0 := All.of.All.All_Imp.fin this h₁
  have := Sum_Sqrt.le.SqrtMul_Sum.of.All_Ge_0.cauchy_schwarz h_Ge_0
  simp only [Finset.card_range] at this
  have h_Le := Le.of.Le.Le h_Le this
  have h_Eq := EqMulS.of.Eq h₂ n
  rw [EqMulDiv.of.Ne_0 (by simp [h₀] : (n : ℝ) ≠ 0)] at h_Eq
  rw [h_Eq] at h_Le
  rw [Mul_Mul.comm] at h_Le
  rw [Mul.eq.Square] at h_Le
  rw [Mul.comm] at h_Le
  have := Sum.ge.Zero.of.All_Ge_0 h_Ge_0
  have h_n : (n : ℝ) > 0 := by
    simp
    apply Gt_0.of.Ne_0 h₀
  have := GeDivS.of.Ge.Gt_0 this h_n
  norm_num at this
  rw [h_Eq] at this
  rw [EqDivMul.of.Ne_0 (by simp [h₀] : (n : ℝ) ≠ 0)] at this
  rw [← EqSquareSqrt.of.Ge_0 this] at h_Le
  rwa [SqrtMulSquareS.eq.Mul.of.Ge_0.Ge_0 (by norm_num) (by apply GeSqrt_0)] at h_Le


-- created on 2025-04-06
-- updated on 2025-04-28

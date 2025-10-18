import sympy.sets.sets
import Lemma.Finset.Any_Gt.of.All_Ge.Any_Ne
import Lemma.Nat.Gt_0.of.Ne_0
import Lemma.Algebra.Root_Add_2.lt.Sqrt.of.Gt_1.Gt_0
import Lemma.Set.Lt.of.In_Range
import Lemma.Real.Sum_Root.lt.Mul_Sqrt.of.EqDivSum.All_Ge_1.Gt_1.Gt_1
import Lemma.Real.All_LeRoot_Sqrt.of.All_Ge_1
import Lemma.Finset.LtSumS.of.All_Le.Any_Lt
import Lemma.Real.Sum_Sqrt.le.Mul_Sqrt.of.EqDivSum.All_Ge_1.Ne_0
import Lemma.Nat.Lt.of.Lt.Le
open Algebra Set Finset Real Nat


/--
Given a sequence \( \{x_i\}_{i=0}^{n-1} \) with \( n > 1 \), where each \( x_i \geq 1 \) and at least one \( x_i \neq 1 \), and the average \( \frac{1}{n}\sum_{i=0}^{n-1} x_i = x_n \), this lemma establishes that the sum of the terms raised to the power \( \frac{1}{i+2} \) is strictly less than \( n \times \sqrt{x_n} \).
The proof leverages inequalities between roots and the Cauchy-Schwarz inequality, ensuring the strictness due to the presence of elements greater than 1.
-/
@[main]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ}
-- given
  (h₀ : n > 1)
  (h₁ : ∀ i ∈ range n, x i ≥ 1)
  (h₂ : ∃ i ∈ range n, x i ≠ 1)
  (h₃ : (∑ i ∈ range n, x i) / n = x n) :
-- imply
  ∑ i ∈ range n, (x i) ^ (1 / (i + 2) : ℝ) < n * √(x n) := by
-- proof
  have := Any_Gt.of.All_Ge.Any_Ne h₁ h₂
  let ⟨i, h⟩ := this
  let ⟨h_In, h_Gt⟩ := h
  have := Lt.of.In_Range h_In
  have h_n : n > 0 := by
    linarith [this]
  by_cases h : i = 0
  ·
    rw [h] at h_Gt
    exact Sum_Root.lt.Mul_Sqrt.of.EqDivSum.All_Ge_1.Gt_1.Gt_1 h₀ h₁ h_Gt h₃
  ·
    have h_All := All_LeRoot_Sqrt.of.All_Ge_1 h₁
    have h := Gt_0.of.Ne_0 h
    have h := Root_Add_2.lt.Sqrt.of.Gt_1.Gt_0 h_Gt h
    have h_Any : ∃ i ∈ range n, (x i) ^ (1 / (i + 2) : ℝ) < √(x i) := by
      use i
    have h_Lt := LtSumS.of.All_Le.Any_Lt h_All h_Any
    have := Sum_Sqrt.le.Mul_Sqrt.of.EqDivSum.All_Ge_1.Ne_0 (by linarith [h₀]) h₁ h₃
    exact Lt.of.Lt.Le h_Lt this


-- created on 2025-04-06
-- updated on 2025-04-07

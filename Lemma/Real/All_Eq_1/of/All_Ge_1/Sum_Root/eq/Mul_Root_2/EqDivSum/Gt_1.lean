import sympy.sets.sets
import Lemma.Real.Sqrt.eq.Root_2
import Lemma.Real.Sum_Root.lt.Mul_Sqrt.of.EqDivSum.Any_Ne_1.All_Ge_1.Gt_1
import Lemma.Nat.Ne.of.Lt
import Lemma.Finset.Any_Not.of.NotAll
open Finset Real Nat


@[main]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ}
-- given
  (h₀ : n > 1)
  (h₁ : (∑ i ∈ range n, x i) / n = x n)
  (h₂ : (∑ i ∈ range n, (x i) ^ (1 / (i + 2) : ℝ)) = n * (x n) ^ (1 / 2 : ℝ))
  (h₃ : ∀ i ∈ range n, x i ≥ 1) :
-- imply
  ∀ i ∈ range n, x i = 1 := by
-- proof
  rw [Root_2.eq.Sqrt] at h₂
  by_contra h
  have h := Any_Not.of.NotAll h
  have := Sum_Root.lt.Mul_Sqrt.of.EqDivSum.Any_Ne_1.All_Ge_1.Gt_1 h₀ h₃ h h₁
  have := Ne.of.Lt this
  contradiction


-- created on 2025-04-06
-- updated on 2025-04-26

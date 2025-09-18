import sympy.sets.sets
import Lemma.Algebra.Sqrt.eq.Root_2
import Lemma.Logic.Any_Not.of.NotAll
import Lemma.Algebra.Ne.of.Lt
import Lemma.Algebra.Sum_Root.lt.Mul_Sqrt.of.EqDivSum.Any_Ne_1.All_Ge_1.Gt_1
open Algebra Logic


/--
Given a natural number \( n > 1 \) and a sequence \( \{x_i\} \) where each \( x_i \geq 1 \), if the sum of \( x_i^{1/(i+2)} \) for \( i \) in the range \( 1 \) to \( n \) equals \( n \sqrt{x_n} \) and the average of \( \{x_i\} \) is \( x_n \), then all \( x_i \) must be equal to \( 1 \).
-/
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
  have h := Any_Not.of.NotAll.fin h
  have := Sum_Root.lt.Mul_Sqrt.of.EqDivSum.Any_Ne_1.All_Ge_1.Gt_1 h₀ h₃ h h₁
  have := Ne.of.Lt this
  contradiction


-- created on 2025-04-06
-- updated on 2025-04-26

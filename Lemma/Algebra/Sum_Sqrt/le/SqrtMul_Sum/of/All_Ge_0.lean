import Lemma.Algebra.SquareSum_Sqrt.le.Mul_Sum.of.All_Ge_0
import Lemma.Algebra.Le_Sqrt.of.LeSquare
open Algebra


@[main]
private lemma cauchy_schwarz
  {s : Finset ℕ}
  {x : ℕ → ℝ}
-- given
  (h : ∀ i ∈ s, x i ≥ 0) :
-- imply
  ∑ i ∈ s, √(x i) ≤ √(s.card * ∑ i ∈ s, x i) := by
-- proof
  have := SquareSum_Sqrt.le.Mul_Sum.of.All_Ge_0.cauchy_schwarz (s := s) (x := x) h
  have := Le_Sqrt.of.LeSquare this
  assumption


-- created on 2025-06-06

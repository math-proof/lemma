import Lemma.Finset.SquareSum.le.Mul_Sum_Square
import Lemma.Real.EqSquareSqrt.of.Ge_0
import Lemma.Bool.All.of.All.All_Imp
import Lemma.Finset.EqSumS.of.All_Eq
open Bool Finset Real


@[main]
private lemma cauchy_schwarz
  {s : Finset ℕ}
  {x : ℕ → ℝ}
-- given
  (h : ∀ i ∈ s, x i ≥ 0) :
-- imply
  (∑ i ∈ s, √(x i))² ≤ s.card * ∑ i ∈ s, x i := by
-- proof
  have h_Le := SquareSum.le.Mul_Sum_Square.cauchy_schwarz (s := s) (x := fun i => √(x i))
  have : ∀ t : ℝ, t ≥ 0 → (√t)² = t := by
    intro t h
    apply EqSquareSqrt.of.Ge_0 h
  have := All.of.All.All_Imp.fin this h
  rwa [EqSumS.of.All_Eq this] at h_Le


-- created on 2025-06-06

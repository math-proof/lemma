import Lemma.Finset.SquareSum_Mul.le.MulSumS_Square
import Lemma.Nat.Mul
open Nat Finset


@[main]
private lemma cauchy_schwarz
  [DecidableEq ι]
  -- given
  (s : Finset ι)
  (x : ι → ℝ) :
-- imply
  (∑ i ∈ s, x i)² ≤ s.card * ∑ i ∈ s, (x i)² := by
-- proof
  have := SquareSum_Mul.le.MulSumS_Square.cauchy_schwarz (s := s) (a := x) (b := fun i => 1)
  norm_num at this
  rwa [Mul.comm] at this


-- created on 2025-06-06

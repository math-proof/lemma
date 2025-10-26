import Lemma.Bool.Delta.eq.Bool
import Lemma.Set.Bool.in.Finset
open Set Bool


@[main]
private lemma main
  [DecidableEq α]
-- given
  (x y : α) :
-- imply
  KroneckerDelta x y ∈ ({0, 1} : Set ℕ) := by
-- proof
  rw [Delta.eq.Bool]
  apply Bool.in.Finset


-- created on 2025-06-01

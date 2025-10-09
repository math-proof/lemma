import Lemma.Nat.Ge.of.NotLt
import Lemma.List.GetElemRange.eq.None.of.Ge
open List Nat


@[main, mp, mpr]
private lemma main
-- given
  (n i j : ℕ) :
-- imply
  (List.range n)[i]? = some j ↔ i < n ∧ i = j := by
-- proof
  by_cases hi : i < n <;>
    simp [hi]


-- created on 2025-05-10

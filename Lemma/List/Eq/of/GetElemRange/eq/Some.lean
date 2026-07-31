import Lemma.List.GetElemRange.eq.None.of.Ge
import Lemma.Nat.NotLt.is.Ge
open List Nat


@[main]
private lemma main
  {n i j : ℕ}
-- given
  (h : (List.range n)[i]? = some j) :
-- imply
  i = j := by
-- proof
  by_cases i < n <;>
    aesop


-- created on 2025-06-02

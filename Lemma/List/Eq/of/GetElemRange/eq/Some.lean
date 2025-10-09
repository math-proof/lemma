import Lemma.List.GetElemRange.eq.None.of.Ge
import Lemma.Nat.Ge.of.NotLt
open List Nat


@[main]
private lemma main
  {n i j : ℕ}
-- given
  (h : (List.range n)[i]? = some j) :
-- imply
  i = j := by
-- proof
  by_cases hi : i < n
  ·
    rw [List.getElem?_range hi] at h
    simp_all
  ·
    have hi := Ge.of.NotLt hi
    have := GetElemRange.eq.None.of.Ge hi
    rw [this] at h
    contradiction


-- created on 2025-06-02

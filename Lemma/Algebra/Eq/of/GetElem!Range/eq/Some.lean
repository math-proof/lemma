import Lemma.Algebra.GetElem!Range.eq.None.of.Ge
open Algebra


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
    have := GetElem!Range.eq.None.of.Ge hi
    rw [this] at h
    contradiction


-- created on 2025-06-02

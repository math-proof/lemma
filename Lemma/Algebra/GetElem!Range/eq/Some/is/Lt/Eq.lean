import stdlib.List.Vector
import Lemma.Algebra.Ge.of.NotLt
import Lemma.Algebra.GetElem!Range.eq.None.of.Ge
open Algebra


@[main, mp, mpr]
private lemma main
-- given
  (n i j : ℕ) :
-- imply
  (List.range n)[i]? = some j ↔ i < n ∧ i = j := by
-- proof
  by_cases hi : i < n
  ·
    simp [hi]
  ·
    simp [hi]
    have hi := Ge.of.NotLt hi
    have := GetElem!Range.eq.None.of.Ge hi
    rw [this]
    simp


-- created on 2025-05-10

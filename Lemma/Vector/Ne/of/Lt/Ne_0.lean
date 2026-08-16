import Lemma.Vector.Lt.is.All_Lt
open Vector


/--
| attributes | lemma |
| :---: | :---: |
| main | Vector.Ne.of.Lt.Ne_0 |
| comm 2 | Vector.Ne.of.Gt.Ne_0 |
-/
@[main, comm 2]
private lemma main
  [Preorder α]
  {x y : List.Vector α n}
-- given
  (h_n : n ≠ 0)
  (h : x < y) :
-- imply
  x ≠ y := by
-- proof
  intro heq
  subst heq
  rw [Lt.is.All_Lt] at h
  exact (lt_irrefl _ (h ⟨0, Nat.pos_of_ne_zero h_n⟩)).elim


-- created on 2026-08-16

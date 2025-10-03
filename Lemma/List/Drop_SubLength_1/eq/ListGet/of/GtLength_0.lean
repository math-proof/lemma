import Lemma.List.Drop.eq.Cons_Drop_Add_1.of.Lt_Length
import Lemma.Algebra.EqAddSub.of.Ge
import Lemma.List.Drop.eq.Nil
open Algebra List


@[main]
private lemma main
  {v : List α}
-- given
  (h : v.length > 0) :
-- imply
  v.drop (v.length - 1) = [v[v.length - 1]] := by
-- proof
  rw [Drop.eq.Cons_Drop_Add_1.of.Lt_Length (by simp_all)]
  rw [EqAddSub.of.Ge (by linarith)]
  rw [Drop.eq.Nil]


-- created on 2025-06-17

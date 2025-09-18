import Lemma.Algebra.AddAdd
import Lemma.Algebra.InsertIdxCons.eq.Cons_InsertIdx
open Algebra


@[main]
private lemma main
-- given
  (a b : List α)
  (i : ℕ)
  (x : α) :
-- imply
  (a ++ b).insertIdx (a.length + i) x = a ++ b.insertIdx i x := by
-- proof
  induction a with
  | nil =>
    simp_all
  | cons head tail ih =>
    simp
    rw [AddAdd.comm]
    simp_all [InsertIdxCons.eq.Cons_InsertIdx]


-- created on 2025-06-09

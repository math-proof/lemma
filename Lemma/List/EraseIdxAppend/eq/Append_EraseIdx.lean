import Lemma.Algebra.AddAdd
open Algebra


@[main]
private lemma main
-- given
  (a b : List α)
  (i : ℕ):
-- imply
  (a ++ b).eraseIdx (a.length + i) = a ++ b.eraseIdx i := by
-- proof
  induction a with
  | nil =>
    simp_all
  | cons head tail ih =>
    simp
    rw [AddAdd.comm]
    simp_all


-- created on 2025-06-09

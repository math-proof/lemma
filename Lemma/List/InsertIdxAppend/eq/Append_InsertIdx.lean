import Lemma.Nat.AddAdd
open Nat


@[main]
private lemma main
-- given
  (a b : List α)
  (i : ℕ)
  (x : α) :
-- imply
  (a ++ b).insertIdx (a.length + i) x = a ++ b.insertIdx i x := by
-- proof
  induction a <;>
    simp_all [AddAdd.comm]


-- created on 2025-06-09

import Lemma.Nat.AddAdd
open Nat


@[main]
private lemma main
-- given
  (a b : List α)
  (i : ℕ):
-- imply
  (a ++ b).eraseIdx (a.length + i) = a ++ b.eraseIdx i := by
-- proof
  grind


-- created on 2025-06-09

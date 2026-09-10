import Lemma.Nat.Delta.eq.Ite
open Nat


@[main]
private lemma Comm
  [DecidableEq α]
-- given
  (x y : α) :
-- imply
  KroneckerDelta x y = KroneckerDelta y x := by
-- proof
  simp [Delta.eq.Ite]
  grind


-- created on 2021-12-29

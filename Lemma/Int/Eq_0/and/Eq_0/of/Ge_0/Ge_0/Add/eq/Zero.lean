import Lemma.Bool.NotAnd.is.OrNotS
import Lemma.Bool.Ne.is.NotEq
import Lemma.Algebra.Gt.is.Ge.Ne
import Lemma.Nat.Add.gt.Zero.of.Gt_0.Ge_0
import Lemma.Nat.Add.gt.Zero.of.Ge_0.Gt_0
import Lemma.Nat.Ne.of.Gt
open Algebra Bool Nat


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {x y : α}
-- given
  (h_x : x ≥ 0)
  (h_y : y ≥ 0)
  (h_Add : x + y = 0) :
-- imply
  x = 0 ∧ y = 0 := by
-- proof
  by_contra h
  rw [NotAnd.is.OrNotS] at h
  rw [NotEq.is.Ne, NotEq.is.Ne] at h
  cases h with
  | inl h =>
    have := Gt.of.Ge.Ne h_x h
    have := Add.gt.Zero.of.Gt_0.Ge_0 this h_y
    have := Ne.of.Gt this
    contradiction
  | inr h =>
    have := Gt.of.Ge.Ne h_y h
    have := Add.gt.Zero.of.Ge_0.Gt_0 h_x this
    have := Ne.of.Gt this
    contradiction


-- created on 2025-01-17
-- updated on 2025-03-30

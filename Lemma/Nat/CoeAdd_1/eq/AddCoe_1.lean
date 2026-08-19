import Lemma.Nat.CoeAdd.eq.AddCoeS
import Lemma.Nat.OfNat.eq.Cast
open Nat


@[main, comm]
private lemma main
  [AddMonoidWithOne α]
-- given
  (n : ℕ) :
-- imply
  (n + 1 : ℕ) = (n + 1 : α) :=
-- proof
  Nat.cast_succ n


@[main, comm]
private lemma ring
  [Semiring α]
-- given
  (n : ℕ) :
-- imply
  (n + 1 : ℕ) = (n + 1 : α) := by
-- proof
  rw [OfNat.eq.Cast (α := α)]
  rw [AddCoeS.eq.CoeAdd]


-- created on 2025-05-23
-- updated on 2026-08-19

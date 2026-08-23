import Lemma.Nat.Delta.eq.Ite
open Nat


@[main]
private lemma main
  [DecidableEq ι]
  [Semiring α]
-- given
  (f : ι → α)
  (x y : ι) :
-- imply
  f x * (KroneckerDelta x y : α) = f y * (KroneckerDelta x y : α) := by
-- proof
  rw [Delta.eq.Ite]
  split_ifs with h
  ·
    rw [h]
  ·
    simp


-- created on 2023-03-17
-- updated on 2026-08-23

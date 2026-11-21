import Lemma.Rat.FloorDiv.eq.Zero.of.Lt
import Theorem.Nat.Gt_0
open Rat


@[path]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {n : ℕ}
-- given
  (j : Fin n) :
-- imply
  ⌊((j : ℕ) : α) / n⌋ = 0 := by
-- proof
  apply FloorDiv.eq.Zero.of.Lt
  simp


-- created on 2025-07-06
-- updated on 2026-11-21

import Theorem.Nat.OfNat.eq.Cast
import Lemma.Int.Div.eq.FloorDiv.of.Gt_0
open Int Nat


@[path]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
  {n d : ℕ}
-- given
  (h : d > 0) :
-- imply
  n / d = ⌊n / (d : α)⌋ := by
-- proof
  have hd : (d : ℤ) > 0 := by exact_mod_cast h
  simp [Div.eq.FloorDiv.of.Gt_0 (α := α) hd]


-- created on 2025-03-17
-- updated on 2026-11-20

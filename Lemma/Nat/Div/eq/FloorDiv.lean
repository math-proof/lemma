import Lemma.Nat.Div.eq.FloorDiv.of.Gt_0
open Nat


@[path]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
  {n d : ℕ} :
-- imply
  (n / d : ℕ) = ⌊n / (d : α)⌋ := by
-- proof
  if h_d : d = 0 then
    rw [h_d]
    norm_num
  else
    have := Nat.pos_of_ne_zero h_d
    apply Div.eq.FloorDiv.of.Gt_0 this


-- created on 2025-07-06
-- updated on 2026-11-20

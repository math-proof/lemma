import Lemma.Nat.Sub.eq.Zero
open Nat


@[main]
private lemma main
  [AddGroup α]
  {a b : α}
-- given
  (h : a - b ≠ 0) :
-- imply
  a ≠ b := by
-- proof
  by_contra h'
  rw [h'] at h
  rw [Sub.eq.Zero] at h
  contradiction


-- created on 2025-03-30

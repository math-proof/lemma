import Lemma.List.EqRotate
import Lemma.Nat.EqAdd_Sub.of.Ge
open List Nat


@[main]
private lemma main
  {s : List α}
-- given
  (h : i ≤ s.length) :
-- imply
  (s.rotate i).rotate (s.length - i) = s := by
-- proof
  rw [List.rotate_rotate]
  rw [EqAdd_Sub.of.Ge (by omega)]
  apply EqRotate


-- created on 2025-10-14
-- updated on 2025-10-18

import Lemma.List.EqRotate_Length
import Lemma.Nat.EqAdd_Sub.of.Ge
import Lemma.List.RotateRotate.eq.Rotate_Add
open List Nat


@[main, comm]
private lemma main
  {s : List α}
-- given
  (h : i ≤ s.length) :
-- imply
  (s.rotate i).rotate (s.length - i) = s := by
-- proof
  rw [RotateRotate.eq.Rotate_Add]
  rw [EqAdd_Sub.of.Ge (by omega)]
  apply EqRotate_Length


-- created on 2025-10-14
-- updated on 2025-10-19

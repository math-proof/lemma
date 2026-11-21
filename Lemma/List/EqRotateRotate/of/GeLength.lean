import Lemma.List.EqRotate_Length
import Theorem.Nat.EqAdd_Sub.of.Ge
import Lemma.List.RotateRotate.eq.Rotate_Add
open List Nat


/--
| attributes | lemma |
| :---: | :---: |
| path | List.EqRotateRotate.of.GeLength |
| comm | List.Eq_RotateRotate.of.GeLength |
-/
@[path, comm]
private lemma main
  {s : List α}
-- given
  (h : s.length ≥ i) :
-- imply
  (s.rotate i).rotate (s.length - i) = s := by
-- proof
  rw [RotateRotate.eq.Rotate_Add]
  rw [EqAdd_Sub.of.Ge h]
  apply EqRotate_Length


-- created on 2025-10-14
-- updated on 2026-11-21

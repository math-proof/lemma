import Lemma.Nat.EqSub.of.EqAdd
import Lemma.List.EqRotateRotate.of.Le_Length.Eq_Length
open Nat List


@[main]
private lemma main
  {s : List α}
-- given
  (h : i + j = s.length) :
-- imply
  (s.rotate i).rotate j = s := by
-- proof
  have h := Eq_Sub.of.EqAdd.left h
  rw [h]
  apply EqRotateRotate.of.Le_Length.Eq_Length rfl (by omega)


-- created on 2025-10-15

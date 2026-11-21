import Theorem.Nat.EqSub.of.EqAdd
import Lemma.List.EqRotateRotate.of.GeLength.Eq_Length
open Nat List


@[path]
private lemma main
  {s : List α}
-- given
  (h : i + j = s.length) :
-- imply
  (s.rotate i).rotate j = s := by
-- proof
  rw [← EqSub.of.EqAdd.left h]
  apply EqRotateRotate.of.GeLength.Eq_Length rfl (by omega)


-- created on 2025-10-15
-- updated on 2026-11-20

import Theorem.Nat.EqSub.of.EqAdd
import Lemma.List.TakeRotate.eq.Drop.of.GeLength
open Nat List


@[path]
private lemma main
  {s : List α}
-- given
  (h : s.length = i + j) :
-- imply
  (s.rotate i).take j = s.drop i := by
-- proof
  rw [← EqSub.of.EqAdd.left h.symm]
  apply TakeRotate.eq.Drop.of.GeLength
  omega


-- created on 2025-10-23
-- updated on 2026-11-20

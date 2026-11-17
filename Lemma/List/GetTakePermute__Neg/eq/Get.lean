import Initialize.Tactic.Attr.Basic
import Lemma.List.Get.of.Eq.GtLength
import Lemma.List.TakePermute__Neg.eq.ListGet
import Theorem.Data.List.List.Part2
open List Nat


@[path]
private lemma main
  {s : List α}
-- given
  (i : Fin s.length) :
-- imply
  have h := Gt_0 i
  have : (s.permute i (-i)).length > 0 := by simpa [List.length_permute]
  (s.permute i (-i))[0] = s[i] := by
-- proof
  intro h h_length
  have := TakePermute__Neg.eq.ListGet i
  have := Get.of.Eq.GtLength (i := 0) (by simp; omega) this
  simpa


-- created on 2025-10-27

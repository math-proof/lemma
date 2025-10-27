import Lemma.List.EqGetS.of.Eq.Lt_Length
import Lemma.List.TakePermute__Neg.eq.ListGet
import Lemma.Nat.Gt_0
open List Nat


@[main]
private lemma main
  {s : List α}
-- given
  (i : Fin s.length) :
-- imply
  have h := Gt_0 i
  have : (s.permute i (-i)).length > 0 := by simpa
  (s.permute i (-i))[0] = s[i] := by
-- proof
  intro h h_length
  have := TakePermute__Neg.eq.ListGet i
  have := EqGetS.of.Eq.Lt_Length (i := 0) (by simp; omega) this
  simpa


-- created on 2025-10-27

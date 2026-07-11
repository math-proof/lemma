import Lemma.List.Drop.eq.ListGet.of.GeLength_1
import Lemma.List.DropAppend.eq.AppendDrop.of.GeLength
import Lemma.List.DropCons.eq.Drop_Sub_1.of.Gt_0
open List Nat


@[main]
private lemma main
  {s : List α}
-- given
  (h : s.length > 0)
  (n a : α) :
-- imply
  (n :: (s ++ [a])).drop s.length = [s[s.length - 1], a] := by
-- proof
  rw [DropCons.eq.Drop_Sub_1.of.Gt_0 (by grind)]
  rw [DropAppend.eq.AppendDrop.of.GeLength (by grind)]
  rw [Drop.eq.ListGet.of.GeLength_1 (by grind)]
  simp


-- created on 2026-07-11

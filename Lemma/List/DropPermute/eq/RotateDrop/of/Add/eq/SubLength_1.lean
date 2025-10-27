import Lemma.List.DropPermute.eq.RotateDrop.of.Add.ge.SubLength_1
open List


@[main]
private lemma main
  {s : List α}
  {i : Fin s.length}
-- given
  (h : i + d = s.length - 1) :
-- imply
  (s.permute i ↑(d)).drop i = (s.drop i).rotate 1 := by
-- proof
  apply DropPermute.eq.RotateDrop.of.Add.ge.SubLength_1
  omega


-- created on 2025-10-22
-- updated on 2025-10-27

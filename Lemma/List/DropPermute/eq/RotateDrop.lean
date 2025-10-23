import Lemma.List.DropPermute.eq.RotateDrop.of.Add.eq.SubLength_1
open List


@[main]
private lemma main
  {s : List α}
-- given
  (i : Fin s.length) :
-- imply
  (s.permute i ↑(s.length - 1 - i)).drop i = (s.drop i).rotate 1 := by
-- proof
  apply DropPermute.eq.RotateDrop.of.Add.eq.SubLength_1
  omega


-- created on 2025-10-14
-- updated on 2025-10-23

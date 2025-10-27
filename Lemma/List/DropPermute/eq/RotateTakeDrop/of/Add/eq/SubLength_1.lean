import Lemma.List.DropPermute.eq.RotateTakeDrop.of.Add.ge.SubLength_1
open List


@[main, comm]
private lemma main
  {s : List α}
  {i : Fin s.length}
  {d : ℕ}
-- given
  (h : i + d = s.length - 1) :
-- imply
  (s.permute i d).drop i = ((s.drop i).take (d + 1)).rotate 1 := by
-- proof
  apply DropPermute.eq.RotateTakeDrop.of.Add.ge.SubLength_1
  omega


-- created on 2025-10-23
-- updated on 2025-10-27

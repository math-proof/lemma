import Lemma.List.DropPermute.eq.RotateTakeDrop.of.Add.ge.SubLength_1
import Lemma.List.EqTake.of.Ge_Length
open List


@[main]
private lemma main
  {s : List α}
  {i : Fin s.length}
-- given
  (h : i + d ≥ s.length - 1) :
-- imply
  (s.permute i ↑(d)).drop i = (s.drop i).rotate 1 := by
-- proof
  rw [DropPermute.eq.RotateTakeDrop.of.Add.ge.SubLength_1 h]
  congr
  apply EqTake.of.Ge_Length
  simp
  omega


-- created on 2025-10-27

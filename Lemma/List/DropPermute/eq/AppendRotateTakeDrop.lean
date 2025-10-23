import Lemma.List.Permute.eq.Append_AppendRotateTakeDrop
import Lemma.List.EqDropAppend.of.Eq_Length
import Lemma.Nat.AddAdd.eq.Add_Add
open List Nat


@[main, comm]
private lemma main
  {s : List α}
-- given
  (i : Fin s.length)
  (d : ℕ) :
-- imply
  (s.permute i d).drop i = ((s.drop i).take (d + 1)).rotate 1 ++ s.drop (i + d + 1) := by
-- proof
  rw [Permute.eq.Append_AppendRotateTakeDrop]
  rw [EqDropAppend.of.Eq_Length]
  ·
    simp [Add_Add.eq.AddAdd]
  ·
    simp


-- created on 2025-10-14

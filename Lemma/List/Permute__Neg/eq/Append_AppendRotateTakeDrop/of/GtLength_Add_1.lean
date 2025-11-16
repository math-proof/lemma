import Lemma.List.DropTake.eq.TakeDrop
import Lemma.List.Permute__Neg.eq.Append_AppendRotateDropTake
import Lemma.List.TakeDrop.eq.DropTake
import Lemma.List.TakeTake.eq.Take.of.Gt
import Lemma.Nat.AddAdd.eq.Add_Add
open List Nat


@[main, comm]
private lemma main
  {s : List α}
  {i d : ℕ}
-- given
  (h : s.length > i + d + 1) :
-- imply
  s.permute ⟨i + d, by grind⟩ (-d) = s.take i ++ (((s.drop i).take (d + 1)).rotate d ++ s.drop (i + d + 1)) := by
-- proof
  rw [Permute__Neg.eq.Append_AppendRotateDropTake]
  simp
  rw [TakeTake.eq.Take.of.Gt (by omega)]
  rw [AddAdd.eq.Add_Add]
  rw [← TakeDrop.eq.DropTake]


-- created on 2025-10-29

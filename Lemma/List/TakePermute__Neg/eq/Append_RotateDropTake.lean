import Lemma.List.EqTakeAppend.of.Eq_Length
import Lemma.List.Permute__Neg.eq.Append_AppendRotateTakeDrop
import Lemma.List.TakeTake.eq.Take.of.Ge
open List


@[main, comm]
private lemma main
  {s : List α}
-- given
  (i : Fin s.length)
  (d : ℕ) :
-- imply
  (s.permute i (-d)).take (i + 1) = s.take (i - d) ++ ((s.take (i + 1)).drop (i - d)).rotate (d ⊓ i) := by
-- proof
  rw [Permute__Neg.eq.Append_AppendRotateTakeDrop]
  rw [EqTakeAppend.of.Eq_Length]
  ·
    rw [TakeTake.eq.Take.of.Ge (by omega)]
  ·
    simp
    grind


-- created on 2025-10-27

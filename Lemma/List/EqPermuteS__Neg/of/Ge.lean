import Lemma.List.Permute__Neg.eq.Append_AppendRotateTakeDrop
import Lemma.List.TakeTake.eq.Take.of.Gt
import Lemma.Nat.EqMin.of.Ge
import Lemma.Nat.Sub.eq.Zero.of.Le
open List Nat


@[main]
private lemma main
  {a : List α}
  {i : Fin a.length}
  {d : ℕ}
-- given
  (h : d ≥ i) :
-- imply
  a.permute i (-d) = a.permute i (-i) := by
-- proof
  rw [Permute__Neg.eq.Append_AppendRotateTakeDrop]
  rw [EqMin.of.Ge h]
  rw [TakeTake.eq.Take.of.Gt (by omega)]
  simp [Sub.eq.Zero.of.Le h]
  rw [Permute__Neg.eq.Append_AppendRotateTakeDrop]
  simp


-- created on 2025-10-27

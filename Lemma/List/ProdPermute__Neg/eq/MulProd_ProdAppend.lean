import Lemma.List.Permute__Neg.eq.Append_AppendRotateTakeDrop
import Lemma.List.TakeTake.eq.Take.of.Gt
open List


@[main]
private lemma main
  [Monoid α]
  {s : List α}
-- given
  (i : Fin s.length)
  (d : ℕ) :
-- imply
  (s.permute i (-d)).prod = (s.take (i - d)).prod * (((s.take (i + 1)).drop (i - d)).rotate (d ⊓ i) ++ s.drop (i + 1)).prod := by
-- proof
  have := Permute__Neg.eq.Append_AppendRotateTakeDrop i d
  rw [TakeTake.eq.Take.of.Gt (by omega)] at this
  have := congrArg List.prod this
  simp at this
  simpa


-- created on 2025-10-28

import Lemma.List.Permute__Neg.eq.Append_AppendRotateDropTake
open List


@[main]
private lemma main
  {s : List α}
  {i : Fin s.length}
  {d : ℕ}
-- given
  (h : i ≤ d) :
-- imply
  s.permute i (-d) = s.permute i (-i) := by
-- proof
  repeat rw [Permute__Neg.eq.Append_AppendRotateDropTake]
  simp_all


-- created on 2025-10-31

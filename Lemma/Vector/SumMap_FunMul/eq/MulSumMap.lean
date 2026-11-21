import Lemma.Vector.SumMapVal.eq.SumMap
open Vector


@[path]
private lemma main
  [Add β] [MulZeroClass β] [RightDistribClass β]
-- given
  (s : List.Vector α n)
  (f : α → β)
  (const : β) :
-- imply
  (s.map fun x => f x * const).sum = (s.map f).sum * const := by
-- proof
  rw [← SumMapVal.eq.SumMap, ← SumMapVal.eq.SumMap]
  induction s.val with
  | nil => simp
  | cons head tail ih =>
    simp [ih, add_mul]


-- created on 2025-10-03
-- updated on 2026-11-20

import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a b : ℝ}
-- given
  (h₀ : Set.Icc a b ≠ ∅) :
-- imply
  a - b ≤ 0 := by
-- proof
  linarith [Set.nonempty_Icc.mp (Set.nonempty_iff_ne_empty.mpr h₀)]


-- created on 2021-05-11
-- updated on 2026-10-26

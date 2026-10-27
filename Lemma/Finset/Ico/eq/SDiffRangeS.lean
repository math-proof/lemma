import Initialize.Tactic.Attr.Basic
import Theorem.Data.Set.Sets


@[path]
private lemma main
-- given
  (i n : ℕ) :
-- imply
  Finset.Ico i n = range n \ range i := by
-- proof
  ext k
  simp [Finset.mem_Ico, Finset.mem_range]
  rw [And.comm]


-- created on 2025-12-30

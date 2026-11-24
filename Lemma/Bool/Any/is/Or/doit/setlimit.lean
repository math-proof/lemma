import Initialize.Tactic.Attr.Basic
import Lemma.Bool.Any.is.Or.doit.outer.setlimit


@[path]
private lemma main
  {x : ℤ → ℝ}
  {a b : ℤ} :
-- imply
  (∃ i ∈ ({a, b} : Set ℤ), x i > 0) ↔ x a > 0 ∨ x b > 0 := by
-- proof
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp, exists_eq_left]


-- created on 2019-02-09
-- updated on 2026-11-24

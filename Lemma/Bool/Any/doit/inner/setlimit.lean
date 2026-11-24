import Initialize.Tactic.Attr.Basic
import Lemma.Bool.Any.limits.swap.subst


@[path]
private lemma main
  {a b : ι}
  {m : ℕ}
  {x : ℕ → ι → Prop} :
-- imply
  (∃ i < m, ∃ j ∈ ({a, b} : Set ι), x i j) ↔ ∃ i < m, x i a ∨ x i b := by
-- proof
  simp


-- created on 2019-02-10
-- updated on 2026-11-24

import Initialize.Tactic.Attr.Basic
import Lemma.Bool.All.of.All.limits.domain_defined.given
open Bool


@[path]
private lemma main
  {m n : ℕ}
  {p : ℕ → Prop}
-- given
  (h : ∀ i < m, p i) :
-- imply
  ∀ i < min m n, p i := by
-- proof
  intro i hi
  simp only [lt_min_iff] at hi
  exact h i hi.1


-- created on 2024-06-25
-- updated on 2026-11-26

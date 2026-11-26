import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic
import Lemma.Bool.Any.of.Any.limits.domain_defined.given
open Bool


@[path]
private lemma main
  {m n : ℕ}
  {p : ℕ → Prop}
-- given
  (h₀ : ∃ i < m, p i)
  (h₁ : m ≤ n) :
-- imply
  ∃ i < min m n, p i := by
-- proof
  simpa only [min_eq_left h₁] using h₀


-- created on 2026-09-27
-- updated on 2026-11-26

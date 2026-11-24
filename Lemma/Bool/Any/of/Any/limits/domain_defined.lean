import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic
import Lemma.Bool.Any.of.Any.limits.domain_defined.given


@[path]
private lemma main
  {m n : ℕ}
  {p : ℕ → Prop}
-- given
  (h₀ : ∃ i ∈ Finset.range m, p i)
  (h₁ : m ≤ n) :
-- imply
  ∃ i ∈ Finset.range (min m n), p i := by
-- proof
  rwa [min_eq_left h₁]




-- created on 2026-09-27
-- updated on 2026-11-24

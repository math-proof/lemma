import Initialize.Tactic.Attr.Basic
import Lemma.Bool.All.of.All.limits.invert
open Bool


@[path]
private lemma main
  {m n : ℕ}
  {p : ℕ → Prop}
-- given
  (h₀ : m ≤ n)
  (h₁ : ∀ i < min m n, p i) :
-- imply
  ∀ i < m, p i := by
-- proof
  rwa [min_eq_left h₀] at h₁


-- created on 2024-06-25
-- updated on 2026-11-26

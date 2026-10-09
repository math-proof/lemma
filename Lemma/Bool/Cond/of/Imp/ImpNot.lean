import Lemma.Bool.Or_Not
open Bool


@[path]
private lemma main
  {p q : Prop}
-- given
  (h₀ : p → q)
  (h₁ : ¬p → q) :
-- imply
  q := by
-- proof
  grind


@[path]
private lemma domain_defined.given
  {f : α → ℝ}
  {x : α}
-- given
  (h₀ : f x ≠ 0)
  (h₁ : f x ≠ 0 → 1 / f x > 0) :
-- imply
  1 / f x > 0 :=
-- proof
  h₁ h₀


-- created on 2018-05-07
-- updated on 2026-09-27

import sympy.Basic


@[main]
private lemma subst
  [DecidableEq α]
  {x y : α}
  {f : α → α → β}
  {g : ℕ → β}
-- given
  (h₀ : x ≠ y)
  (h₁ : g (if x = y then 1 else 0) ≠ f x y) :
-- imply
  g 0 ≠ f x y := by
-- proof
  rwa [if_neg h₀] at h₁


-- created on 2026-09-27

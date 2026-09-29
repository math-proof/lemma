import sympy.Basic


@[main]
private lemma main
  [Preorder α]
  {a b c : α}
-- given
  (h₀ : a > b)
  (h₁ : b > c) :
-- imply
  a > c :=
-- proof
  gt_trans h₀ h₁


@[main]
private lemma subst
  {y b x t k : ℝ}
-- given
  (hk : k > 0)
  (h₀ : y > x * k + b)
  (h₁ : x > t) :
-- imply
  y > t * k + b := by
-- proof
  nlinarith


-- created on 2018-05-19
-- updated on 2026-09-27

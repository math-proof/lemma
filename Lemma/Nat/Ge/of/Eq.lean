import sympy.Basic


@[main]
private lemma main
  [Preorder α]
  {x y : α}
-- given
  (h : x = y) :
-- imply
  x ≥ y := by
-- proof
  rw [h]


@[main]
private lemma relax
  {x y l : ℝ}
-- given
  (h : x = y)
  (h₁ : l ≤ y) :
-- imply
  x ≥ l := by
-- proof
  rw [h]
  exact h₁


@[main]
private lemma relax.upper
  {x y u : ℝ}
-- given
  (h : x = y)
  (h₁ : y ≤ u) :
-- imply
  u ≥ x := by
-- proof
  rw [h]
  exact h₁


-- created on 2021-07-26
-- updated on 2026-09-27

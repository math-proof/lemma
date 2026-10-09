import sympy.Basic


@[path]
private lemma main
  [Preorder α]
  {x y : α}
-- given
  (h : x = y) :
-- imply
  x ≤ y := by
-- proof
  rw [h]


@[path]
private lemma relax
  [Preorder α]
  {a b u : α}
-- given
  (h₀ : a = b)
  (h₁ : b ≤ u) :
-- imply
  a ≤ u :=
-- proof
  h₀ ▸ h₁


-- created on 2021-03-16
-- updated on 2026-09-27

import sympy.Basic


@[path]
private lemma main
  {a b c : α}
  {f : α → α}
-- given
  (h₀ : a = b)
  (h₁ : c = f a) :
-- imply
  c = f b := by
-- proof
  rwa [h₀] at h₁


-- created on 2026-10-11

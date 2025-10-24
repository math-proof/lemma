import sympy.Basic


@[main]
private lemma main
  -- given
  (l₁ l₂ : List α)
  (i : ℕ) :
-- imply
  (l₁ ++ l₂).take i = l₁.take i ++ l₂.take (i - l₁.length) :=
-- proof
  List.take_append


-- created on 2025-10-24

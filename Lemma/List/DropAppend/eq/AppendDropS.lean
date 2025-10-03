import sympy.Basic


@[main]
private lemma main
-- given
  (l₁ l₂ : List α)
  (i : ℕ) :
-- imply
  (l₁ ++ l₂).drop i = l₁.drop i ++ l₂.drop (i - l₁.length) :=
-- proof
  List.drop_append


-- created on 2025-10-03

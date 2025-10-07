import sympy.Basic


@[main]
private lemma main
  [Decidable p]
  {q : Prop}
  {x a b : α}
-- given
  (h₀ : x =
    if p then
      a
    else
      b)
  (h₁ : q)
  (h₂ : ¬(p ∧ q)) :
-- imply
  x = b := by
-- proof
  split_ifs at h₀ <;>
    simp_all


-- created on 2025-03-21

import sympy.Basic


@[main]
private lemma main
  {x y : α}
  {S : Set α}
-- given
  (h₀ : x ∈ S)
  (h₁ : y ∈ S) :
-- imply
  {x, y} ⊆ S := by
-- proof
  intro z hz
  grind


-- created on 2018-03-29

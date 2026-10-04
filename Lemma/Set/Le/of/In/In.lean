import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y a b c : ℤ}
-- given
  (h₀ : x ∈ Set.Ioc a b)
  (h₁ : y ∈ Set.Icc b c) :
-- imply
  x ≤ y := by
-- proof
  exact h₀.2.trans h₁.1


-- created on 2020-05-09

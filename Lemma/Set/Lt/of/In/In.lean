import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b c x y : ℤ}
-- given
  (h₁ : x ∈ Set.Ioc a b)
  (h₂ : y ∈ Set.Ioc b c) :
-- imply
  x < y := by
-- proof
  exact lt_of_le_of_lt (Set.mem_Ioc.mp h₁).2 (Set.mem_Ioc.mp h₂).1


-- created on 2021-02-26

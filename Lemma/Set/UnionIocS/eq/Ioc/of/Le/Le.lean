import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  [LinearOrder α]
  {a b c : α}
-- given
  (h₀ : a ≤ b)
  (h₁ : b ≤ c):
-- imply
  Ioc a b ∪ Ioc b c = Ioc a c :=
-- proof
  Set.Ioc_union_Ioc_eq_Ioc h₀ h₁


-- created on 2025-08-14

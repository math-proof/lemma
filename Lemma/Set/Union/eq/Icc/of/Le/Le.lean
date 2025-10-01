import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  [LinearOrder α]
  {a b x : α}
-- given
  (h₀ : a ≤ x)
  (h₁ : x ≤ b) :
-- imply
  Icc a x ∪ Ioc x b = Icc a b :=
-- proof
  Set.Icc_union_Ioc_eq_Icc h₀ h₁


-- created on 2025-10-01

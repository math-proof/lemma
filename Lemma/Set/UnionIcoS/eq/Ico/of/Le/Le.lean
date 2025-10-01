import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  [LinearOrder α]
  {a b c : α}
-- given
  (h₀ : a ≤ b)
  (h₁ : b ≤ c) :
-- imply
  Ico a b ∪ Ico b c = Ico a c :=
-- proof
  Set.Ico_union_Ico_eq_Ico h₀ h₁


-- created on 2025-10-01

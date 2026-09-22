import sympy.sets.sets
import sympy.Basic


@[main, comm]
private lemma main
  [LinearOrder α]
  {a b c : α}
-- given
  (h₀ : a ≤ c)
  (h₁ : c ≤ b) :
-- imply
  Ico a c ∪ Icc c b = Icc a b :=
-- proof
  Set.Ico_union_Icc_eq_Icc h₀ h₁


-- created on 2026-09-21

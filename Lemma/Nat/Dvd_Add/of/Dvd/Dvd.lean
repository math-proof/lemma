import sympy.Basic


@[main]
private lemma main
  [Add α]
  [Semigroup α]
  [LeftDistribClass α]
  {a b : α}
-- given
  (h₀ : d ∣ a)
  (h₁ : d ∣ b) :
-- imply
  d ∣ a + b :=
-- proof
  dvd_add h₀ h₁


-- created on 2025-10-21

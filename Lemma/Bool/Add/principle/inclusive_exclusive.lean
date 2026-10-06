import sympy.Basic


@[main]
private lemma main
  {p q : Prop}
  [Decidable p]
  [Decidable q] :
-- imply
  Bool.toNat (p ∨ q) + Bool.toNat (p ∧ q) = Bool.toNat p + Bool.toNat q := by
-- proof
  obtain hp | hp := em p <;> obtain hq | hq := em q <;> simp [hp, hq]


-- created on 2018-08-03
-- updated on 2023-04-18

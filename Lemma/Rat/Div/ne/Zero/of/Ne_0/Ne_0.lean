import sympy.Basic


/--
the hypotheses are arranged in the constructor order of division a / b

| attributes | lemma |
| :---: | :---: |
| main | Rat.Div.ne.Zero.of.Ne_0.Ne_0 |
| mt | Rat.Eq_0.of.Ne_0.Div.eq.Zero |
| mt 1 | Rat.Eq_0.of.Div.eq.Zero.Ne_0 |
-/
@[main, mt, mt 1]
private lemma main
  [GroupWithZero α]
  {a b : α}
-- given
  (h₀ : a ≠ 0)
  (h₁ : b ≠ 0) :
-- imply
  a / b ≠ 0 := by
-- proof
  simp_all


-- created on 2025-03-30

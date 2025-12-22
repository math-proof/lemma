import sympy.Basic


/--
the hypotheses are arranged in the constructor order of division a / b

| attributes | lemma |
| :---: | :---: |
| main | Rat.Div.ne.Zero.of.Ne\_0.Ne\_0 |
| mt | Rat.Eq\_0.of.Ne\_0.Div.eq.Zero |
| mt 1 | Rat.Eq\_0.of.Div.eq.Zero.Ne\_0 |
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

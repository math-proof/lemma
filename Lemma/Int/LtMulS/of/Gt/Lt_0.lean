import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Int.LtMulS.of.Gt.Lt_0 |
| comm 2 | Int.GtMulS.of.Lt.Lt_0 |
-/
@[main, comm 2]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {x a b : α}
-- given
  (h₀ : a > b)
  (h₁ : x < 0) :
-- imply
  a * x < b * x :=
-- proof
  mul_lt_mul_of_neg_right h₀ h₁


-- created on 2019-12-15

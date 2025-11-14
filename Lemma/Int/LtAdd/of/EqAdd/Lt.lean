import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Int.LtAdd.of.EqAdd.Lt |
| comm 3 | Int.Gt\_Add.of.Eq\_Add.Gt |
-/
@[main, comm 3]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {a a' b c : α}
-- given
  (h₀ : a' < a)
  (h₁ : a + b = c) :
-- imply
  a' + b < c := by
-- proof
  grind


-- created on 2025-03-20
-- updated on 2025-10-26

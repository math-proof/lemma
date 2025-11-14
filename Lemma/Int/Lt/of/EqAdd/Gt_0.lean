import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Int.Lt.of.EqAdd.Gt_0 |
| comm 2 | Int.Gt.of.Eq\_Add.Gt\_0 |
-/
@[main, comm 2]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {a b c : α}
-- given
  (h₀ : a > 0)
  (h₁ : a + b = c) :
-- imply
  b < c := by
-- proof
  grind


-- created on 2025-03-20
-- updated on 2025-10-25

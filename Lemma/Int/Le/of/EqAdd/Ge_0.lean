import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Int.Le.of.EqAdd.Ge_0 |
| comm 2 | Int.Ge.of.Eq\_Add.Ge\_0 |
-/
@[main, comm 2]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {a b c : α}
-- given
  (h₀ : a ≥ 0)
  (h₁ : c = a + b) :
-- imply
  c ≥ b := by
-- proof
  grind


-- created on 2025-03-20
-- updated on 2025-10-26

import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.EqSubst.of.HEq.Eq |
| comm 3 | Bool.Eq_Subst.of.HEq.Eq |
-/
@[main, comm 3]
private lemma main
  {Vector : α → Sort v}
  {a : Vector n}
  {b : Vector m}
-- given
  (h₁ : n = m)
  (h₀ : HEq a b) :
-- imply
  h₁ ▸ a = b := by
-- proof
  subst h₁
  apply HEq.eq h₀


-- created on 2025-07-25

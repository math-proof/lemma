import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.EqRec.of.HEq.Eq |
| comm 3 | Bool.Eq_Rec.of.HEq.Eq |
-/
@[main, comm 3]
private lemma main
  {Vector : α → Sort v}
  {a : Vector n}
  {b : Vector m}
-- given
  (h₀ : n = m)
  (h₁ : HEq a b) :
-- imply
  Eq.rec a h₀ = b := by
-- proof
  apply HEq.eq
  aesop


-- created on 2025-07-25

import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.EqCast.of.Eq |
| comm | Bool.Eq_Cast.of.Eq |
-/
@[main, comm]
private lemma main
-- given
  (h_n : m = n)
  (i : Fin n) :
-- imply
  cast (congrArg Fin h_n) ⟨i, by grind⟩ = i := by
-- proof
  aesop


-- created on 2025-05-23
-- updated on 2025-05-31

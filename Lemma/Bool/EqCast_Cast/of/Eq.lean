import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.EqCast_Cast.of.Eq |
| comm | Bool.Eq_Cast_Cast.of.Eq |
-/
@[main, comm]
private lemma main
  {α β : Type u}
-- given
  (h : α = β)
  (a : α) :
-- imply
  cast h.symm (cast h a) = a := by
-- proof
  simp


-- created on 2025-06-28

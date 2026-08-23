import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Int.OrEqSAdd.is.OrEqS_Sub |
| comm | Int.OrEqS_Sub.is.OrEqSAdd |
| mp | Int.OrEqS_Sub.of.OrEqSAdd |
| mpr | Int.OrEqSAdd.of.OrEqS_Sub |
-/
@[main, comm, mp, mpr]
private lemma main
  [AddGroup α]
  {x a b c : α} :
-- imply
  x + a = b ∨ x + a = c ↔ x = b - a ∨ x = c - a := by
-- proof
  simp [eq_sub_iff_add_eq]


-- created on 2018-11-28
-- updated on 2026-08-23

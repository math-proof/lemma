import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.Ne.is.NotEq |
| comm | Bool.NotEq.is.Ne |
| mp | Bool.NotEq.of.Ne |
| mpr | Bool.Ne.of.NotEq |
-/
@[main, comm, mp, mpr]
private lemma main
  {a b : α} :
-- imply
  a ≠ b ↔ ¬a = b := by
-- proof
  constructor <;>
  ·
    intro h h_eq
    contradiction


-- created on 2025-04-20

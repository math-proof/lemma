import sympy.functions.elementary.complexes
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Complex.Add_MulI.is.Eq.Eq |
| comm | Complex.Eq.Eq.is.Add_MulI |
| mp | Complex.Eq.Eq.of.Add_MulI |
| mpr | Complex.Add_MulI.of.Eq.Eq |
-/
@[main, comm, mp, mpr]
private lemma main
-- given
  (x y a b : ℝ) :
-- imply
  x + I * y = a + I * b ↔ x = a ∧ y = b := by
-- proof
  constructor
  ·
    intro h
    constructor
    ·
      simpa using congrArg re h
    ·
      simpa using congrArg im h
  ·
    intro ⟨hx, hy⟩
    rw [hx, hy]


-- created on 2018-06-03
-- updated on 2026-08-22

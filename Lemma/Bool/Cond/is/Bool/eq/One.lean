import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.Cond.is.Bool.eq.One |
| comm | Bool.Bool.eq.One.is.Cond |
| mp | Bool.Bool.eq.One.of.Cond |
| mpr | Bool.Cond.of.Bool.eq.One |
-/
@[main, comm, mp, mpr]
private lemma main
  [Decidable p] :
-- imply
  p ↔ Bool.toNat p = 1 := by
-- proof
  grind


-- created on 2025-04-20
-- updated on 2026-07-27

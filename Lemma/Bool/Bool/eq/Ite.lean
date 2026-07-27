import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.Bool.eq.Ite |
| comm | Bool.Ite.eq.Bool |
-/
@[main, comm]
private lemma main
  [Decidable p] :
-- imply
  Bool.toNat p = if p then
    1
  else
    0 := by
-- proof
  grind


-- created on 2025-04-05

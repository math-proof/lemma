import sympy.core.power
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Bool.Bool.eq.SquareBool |
| comm | Bool.SquareBool.eq.Bool |
-/
@[path, comm]
private lemma main
  [Decidable p] :
-- imply
  Bool.toNat p = (Bool.toNat p)² := by
-- proof
  by_cases h : p <;>
    simp [h]


-- created on 2018-03-10

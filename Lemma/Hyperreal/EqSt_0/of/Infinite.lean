import sympy.series.limits
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Hyperreal.EqSt_0.of.Infinite |
| mt | Hyperreal.NotInfinite.of.NeSt_0 |
-/
@[main, mt]
private lemma main
  {x : ℝ*}
-- given
  (h : x → ∞) :
-- imply
  stdPart x = 0 :=
-- proof
  ArchimedeanClass.stdPart_eq_zero.mpr (ne_of_lt h)


-- created on 2025-12-12

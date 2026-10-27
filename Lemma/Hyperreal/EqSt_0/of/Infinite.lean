import Def.Analysis.Real.Limits.Part4
import Initialize.Tactic.Attr.Basic
open ArchimedeanClass


/--
| attributes | lemma |
| :---: | :---: |
| path | Hyperreal.EqSt_0.of.Infinite |
| mt | Hyperreal.NotInfinite.of.NeSt_0 |
-/
@[path, mt]
private lemma main
  {x : ℝ*}
-- given
  (h : x → ∞) :
-- imply
  stdPart x = 0 :=
-- proof
  ArchimedeanClass.stdPart_eq_zero.mpr (ne_of_lt h)


-- created on 2025-12-12

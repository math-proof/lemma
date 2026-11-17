module

public import Def.Analysis.Real.Limits.Basic
public import Initialize.Tactic.Attr.Basic

public section

open ArchimedeanClass


/--
| attributes | lemma |
| :---: | :---: |
| path | Hyperreal.EqSt_0.of.Infinite |
| mt | Hyperreal.NotInfinite.of.NeSt_0 |
-/
@[mt]
public theorem Hyperreal.EqSt_0.of.Infinite
  {x : ℝ*}
-- given
  (h : x → ∞) :
-- imply
  stdPart x = 0 :=
-- proof
  ArchimedeanClass.stdPart_eq_zero.mpr (ne_of_lt h)


-- created on 2025-12-12

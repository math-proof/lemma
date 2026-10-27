import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.StatisticalMechanics.Code.FrontierA.KacWardRawNonbacktrackingSimple
open StatMech StatMech.FrontierA


/--
[KWRawNonbacktrackingSimpleData.vertex_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRawNonbacktrackingSimple.lean)
-/
@[path]
private lemma vertex_injective_eq
  {n : ℕ}
  [NeZero n]
  {vertex : Fin n → ℂ}
-- given
  (h : KWRawNonbacktrackingSimpleData vertex) :
-- imply
  Function.Injective vertex := by
-- proof
  apply StatMech.FrontierA.KWRawNonbacktrackingSimpleData.vertex_injective h


-- created on 2026-10-23

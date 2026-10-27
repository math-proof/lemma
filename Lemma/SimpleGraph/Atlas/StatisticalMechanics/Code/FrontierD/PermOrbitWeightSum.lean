import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.PermOrbitWeightSum
open Equiv Finset StatMech StatMech.FrontierD


/--
[permOrbitWeightSum_eq_visitCount_nsmul_cycleSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/PermOrbitWeightSum.lean)
-/
@[path]
private lemma permOrbitWeightSum_eq_visitCount_nsmul_cycleSum_eq
  [Fintype α]
  [DecidableEq α]
  [AddCommMonoid A]
  {σ : Perm α}
  {d : α}
  {f : α → A} :
-- imply
  permOrbitWeightSum σ d f = (permOrbitVisitCount σ d d) • permCycleClassWeightSum σ d f := by
-- proof
  apply StatMech.FrontierD.permOrbitWeightSum_eq_visitCount_nsmul_cycleSum σ d f

/--
[permOrbitVisitCount_self_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/PermOrbitWeightSum.lean)
-/
@[path]
private lemma permOrbitVisitCount_self_pos_eq
  [Fintype α]
  [DecidableEq α]
  {σ : Perm α}
  {d : α} :
-- imply
  0 < permOrbitVisitCount σ d d := by
-- proof
  apply StatMech.FrontierD.permOrbitVisitCount_self_pos σ d


-- created on 2026-10-23

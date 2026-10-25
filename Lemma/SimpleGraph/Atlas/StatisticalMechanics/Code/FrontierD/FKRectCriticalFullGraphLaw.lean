import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCriticalFullGraphLaw.Part2
open Finset SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectGraphConfigurationExtend_configurationGraphEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCriticalFullGraphLaw.lean)
-/
@[path]
private lemma fkRectGraphConfigurationExtend_configurationGraphEquiv_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectGraphConfigurationExtend R (fkRectConfigurationGraphEquiv R omega) = fkRectFullGraphConfiguration R omega := by
-- proof
  apply StatMech.FrontierD.fkRectGraphConfigurationExtend_configurationGraphEquiv R omega

/--
[fkWeight_fullEdgeConfigEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCriticalFullGraphLaw.lean)
-/
@[path]
private lemma fkWeight_fullEdgeConfigEquiv_eq
  {R : FKRectTorus}
  {p q : Real}
  {omega : R.Configuration} :
-- imply
  FK.fkWeight (fkRectTorusGraph R) p q (fkRectFullEdgeConfigEquiv R omega).1 = fkRectRandomClusterWeight R p q omega := by
-- proof
  apply StatMech.FrontierD.fkWeight_fullEdgeConfigEquiv R p q omega

/--
[fkRectFull_ecz_eventWeight_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCriticalFullGraphLaw.lean)
-/
@[path]
private lemma fkRectFull_ecz_eventWeight_eq_eq
  {R : FKRectTorus}
  {q : Real}
  {A : Set R.Configuration}
-- given
  (hq : 0 < q) :
-- imply
  FK.ecz_eventWeight (fkRectTorusGraph R) (fkRectCriticalP q) q (fkRectFullEdgeEvent R A) = fkRectCriticalEdgeFactor R q * ∑ omega : R.Configuration, A.indicator (fun omega => fkRectCriticalReducedWeight R q omega) omega := by
-- proof
  apply StatMech.FrontierD.fkRectFull_ecz_eventWeight_eq R hq A

/--
[fkRectFull_ecz_fkZEdge_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCriticalFullGraphLaw.lean)
-/
@[path]
private lemma fkRectFull_ecz_fkZEdge_eq_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 0 < q) :
-- imply
  FK.ecz_fkZEdge (fkRectTorusGraph R) (fkRectCriticalP q) q = fkRectCriticalEdgeFactor R q * fkRectCriticalReducedZ R q := by
-- proof
  apply StatMech.FrontierD.fkRectFull_ecz_fkZEdge_eq R hq

/--
[fkRectCriticalEventMass_eq_fullGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCriticalFullGraphLaw.lean)
-/
@[path]
private lemma fkRectCriticalEventMass_eq_fullGraph_eq
  {R : FKRectTorus}
  {q : Real}
  {A : Set R.Configuration}
-- given
  (hq : 1 ≤ q) :
-- imply
  fkRectCriticalEventMass R q A = ∑ sigma : ConfigSpace (Sym2 R.Vertex), (FK.ecz_closeOff (fkRectTorusGraph R) ⁻¹' fkRectFullEdgeEvent R A).indicator (fun _ => (1 : Real)) sigma * FK.fkProb (fkRectTorusGraph R) (fkRectCriticalP q) q sigma := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalEventMass_eq_fullGraph R hq A


-- created on 2026-10-23

import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.FiniteActiveDuality
open Finset SimpleGraph StatMech StatMech.FK


/--
[activeDualConfig_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteActiveDuality.lean)
-/
@[path]
private lemma activeDualConfig_apply_eq
  [Fintype V]
  [Fintype W]
  {edgeDual : G.edgeSet ≃ H.edgeSet}
  {omega : ConfigSpace G.edgeSet}
  {e : H.edgeSet} :
-- imply
  activeDualConfig G H edgeDual omega e = !(omega (edgeDual.symm e)) := by
-- proof
  apply StatMech.FK.activeDualConfig_apply edgeDual omega e

/--
[activeDualConfig_symm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteActiveDuality.lean)
-/
@[path]
private lemma activeDualConfig_symm_apply_eq
  [Fintype V]
  [Fintype W]
  {edgeDual : G.edgeSet ≃ H.edgeSet}
  {eta : ConfigSpace H.edgeSet}
  {e : G.edgeSet} :
-- imply
  (activeDualConfig G H edgeDual).symm eta e = !(eta (edgeDual e)) := by
-- proof
  apply StatMech.FK.activeDualConfig_symm_apply edgeDual eta e

/--
[openCount_extendActive_eq_activeOpenCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteActiveDuality.lean)
-/
@[path]
private lemma openCount_extendActive_eq_activeOpenCount_eq
  [Fintype V]
  [Fintype W]
  {omega : ConfigSpace G.edgeSet} :
-- imply
  openCount G (extendActive G omega) = activeOpenCount G omega := by
-- proof
  apply StatMech.FK.openCount_extendActive_eq_activeOpenCount omega

/--
[activeOpenCount_dualConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteActiveDuality.lean)
-/
@[path]
private lemma activeOpenCount_dualConfig_eq
  [Fintype V]
  [Fintype W]
  {edgeDual : G.edgeSet ≃ H.edgeSet}
  {omega : ConfigSpace G.edgeSet} :
-- imply
  activeOpenCount H (activeDualConfig G H edgeDual omega) = Fintype.card G.edgeSet - activeOpenCount G omega := by
-- proof
  apply StatMech.FK.activeOpenCount_dualConfig edgeDual omega

/--
[activeWeight_eq_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteActiveDuality.lean)
-/
@[path]
private lemma activeWeight_eq_count_eq
  [Fintype V]
  [Fintype W]
  {p q : Real}
  {omega : ConfigSpace G.edgeSet} :
-- imply
  activeWeight G (fun _ => p) q omega = BeffaraDC.edgeProductCount p (Fintype.card G.edgeSet) (activeOpenCount G omega) * q ^ numClusters G (extendActive G omega) := by
-- proof
  apply StatMech.FK.activeWeight_eq_count p q omega

/--
[wiredActiveWeight_eq_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteActiveDuality.lean)
-/
@[path]
private lemma wiredActiveWeight_eq_count_eq
  [Fintype V]
  [Fintype W]
  [DecidablePred boundary]
  {p q : Real}
  {eta : ConfigSpace H.edgeSet}
-- given
  (boundary : W → Prop) :
-- imply
  PeriodicPlanar.wiredActiveWeight H boundary p q eta = BeffaraDC.edgeProductCount p (Fintype.card H.edgeSet) (activeOpenCount H eta) * q ^ numClustersWired H boundary (extendActive H eta) := by
-- proof
  apply StatMech.FK.wiredActiveWeight_eq_count boundary p q eta

/--
[active_free_wired_weight_duality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteActiveDuality.lean)
-/
@[path]
private lemma active_free_wired_weight_duality_eq
  [Fintype V]
  [Fintype W]
  [DecidablePred boundary]
  {edgeDual : G.edgeSet ≃ H.edgeSet}
  {p q : Real}
  {omega : ConfigSpace G.edgeSet}
-- given
  (boundary : W → Prop)
  (hEuler : ActiveFreeWiredEulerIdentity G H boundary edgeDual)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  activeWeight G (fun _ => p) q omega * q ^ (Fintype.card G.edgeSet + 1) = (p / (1 - BeffaraDC.dualParam p q)) ^ Fintype.card G.edgeSet * q ^ Fintype.card V * PeriodicPlanar.wiredActiveWeight H boundary (BeffaraDC.dualParam p q) q (activeDualConfig G H edgeDual omega) := by
-- proof
  apply StatMech.FK.active_free_wired_weight_duality boundary edgeDual hEuler hp hp1 hq omega

/--
[active_free_wired_prob_duality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteActiveDuality.lean)
-/
@[path]
private lemma active_free_wired_prob_duality_eq
  [Fintype V]
  [Fintype W]
  [DecidablePred boundary]
  {edgeDual : G.edgeSet ≃ H.edgeSet}
  {p q : Real}
  {omega : ConfigSpace G.edgeSet}
-- given
  (boundary : W → Prop)
  (hEuler : ActiveFreeWiredEulerIdentity G H boundary edgeDual)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  activeProb G (fun _ => p) q omega = PeriodicPlanar.wiredActiveWeight H boundary (BeffaraDC.dualParam p q) q (activeDualConfig G H edgeDual omega) / PeriodicPlanar.wiredActiveZ H boundary (BeffaraDC.dualParam p q) q := by
-- proof
  apply StatMech.FK.active_free_wired_prob_duality boundary edgeDual hEuler hp hp1 hq omega


-- created on 2026-10-23

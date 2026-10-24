import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSheetGauge
open Finset StatMech StatMech.FrontierA


/--
[multibondCut_configXor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSheetGauge.lean)
-/
@[path]
private lemma multibondCut_configXor_eq
  [Fintype P]
  [DecidableEq P]
-- given
  (ends : P -> V × V)
  (s t : V -> Bool) :
-- imply
  multibondCut ends (multibondConfigXor t s) = multibondCut ends s ∆ multibondCut ends t := by
-- proof
  apply StatMech.FrontierA.multibondCut_configXor ends s t

/--
[multibondIsingWeight_twist_symmDiff_cut_configXor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSheetGauge.lean)
-/
@[path]
private lemma multibondIsingWeight_twist_symmDiff_cut_configXor_eq
  [Fintype P]
  [DecidableEq P]
  {D : Finset P}
-- given
  (ends : P -> V × V)
  (J : P -> Real)
  (s t : V -> Bool) :
-- imply
  multibondIsingWeight ends (multibondTwistCoupling J (D ∆ multibondCut ends t)) (multibondConfigXor t s) = multibondIsingWeight ends (multibondTwistCoupling J D) s := by
-- proof
  apply StatMech.FrontierA.multibondIsingWeight_twist_symmDiff_cut_configXor ends J D s t

/--
[multibondIsingPartition_twist_symmDiff_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSheetGauge.lean)
-/
@[path]
private lemma multibondIsingPartition_twist_symmDiff_cut_eq
  [Fintype P]
  [DecidableEq P]
  {D : Finset P}
-- given
  (ends : P -> V × V)
  (J : P -> Real)
  (t : V -> Bool) :
-- imply
  multibondIsingPartition ends (multibondTwistCoupling J (D ∆ multibondCut ends t)) = multibondIsingPartition ends (multibondTwistCoupling J D) := by
-- proof
  apply StatMech.FrontierA.multibondIsingPartition_twist_symmDiff_cut ends J D t

/--
[multibondDisorderFreeEnergy_symmDiff_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSheetGauge.lean)
-/
@[path]
private lemma multibondDisorderFreeEnergy_symmDiff_cut_eq
  [Fintype P]
  [DecidableEq P]
  {D : Finset P}
-- given
  (ends : P -> V × V)
  (J : P -> Real)
  (t : V -> Bool) :
-- imply
  multibondDisorderFreeEnergy ends J (D ∆ multibondCut ends t) = multibondDisorderFreeEnergy ends J D := by
-- proof
  apply StatMech.FrontierA.multibondDisorderFreeEnergy_symmDiff_cut ends J D t


-- created on 2026-10-23

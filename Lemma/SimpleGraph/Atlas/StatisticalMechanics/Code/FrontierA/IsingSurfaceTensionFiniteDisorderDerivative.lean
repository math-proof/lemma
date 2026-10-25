import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionFiniteDisorderDerivative
open Finset StatMech StatMech.FrontierA


/--
[hasDerivAt_multibondIsingWeight_homogeneous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionFiniteDisorderDerivative.lean)
-/
@[path]
private lemma hasDerivAt_multibondIsingWeight_homogeneous_eq
  [Fintype P]
  [DecidableEq P]
  {J : Real}
-- given
  (ends : P -> V × V)
  (s : V -> Bool) :
-- imply
  HasDerivAt (fun K => multibondIsingWeight ends (fun _ => K) s) (multibondIsingWeight ends (fun _ => J) s * multibondTotalBondSpin ends s) J := by
-- proof
  apply StatMech.FrontierA.hasDerivAt_multibondIsingWeight_homogeneous ends s J

/--
[hasDerivAt_multibondIsingPartition_homogeneous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionFiniteDisorderDerivative.lean)
-/
@[path]
private lemma hasDerivAt_multibondIsingPartition_homogeneous_eq
  [Fintype P]
  [DecidableEq P]
  {J : Real}
-- given
  (ends : P -> V × V) :
-- imply
  HasDerivAt (fun K => multibondIsingPartition ends (fun _ => K)) (∑ s : V -> Bool, multibondIsingWeight ends (fun _ => J) s * multibondTotalBondSpin ends s) J := by
-- proof
  apply StatMech.FrontierA.hasDerivAt_multibondIsingPartition_homogeneous ends J

/--
[hasDerivAt_log_multibondIsingPartition_homogeneous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionFiniteDisorderDerivative.lean)
-/
@[path]
private lemma hasDerivAt_log_multibondIsingPartition_homogeneous_eq
  [Fintype P]
  [DecidableEq P]
  {J : Real}
-- given
  (ends : P -> V × V) :
-- imply
  HasDerivAt (fun K => Real.log (multibondIsingPartition ends (fun _ => K))) (multibondMeanTotalBondSpin ends J) J := by
-- proof
  apply StatMech.FrontierA.hasDerivAt_log_multibondIsingPartition_homogeneous ends J

/--
[hasDerivAt_multibondIsingWeight_twisted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionFiniteDisorderDerivative.lean)
-/
@[path]
private lemma hasDerivAt_multibondIsingWeight_twisted_eq
  [Fintype P]
  [DecidableEq P]
  {D : Finset P}
  {J : Real}
-- given
  (ends : P -> V × V)
  (s : V -> Bool) :
-- imply
  HasDerivAt (fun K => multibondIsingWeight ends (multibondTwistCoupling (fun _ => K) D) s) (multibondIsingWeight ends (multibondTwistCoupling (fun _ => J) D) s * multibondTwistedBondSpin ends D s) J := by
-- proof
  apply StatMech.FrontierA.hasDerivAt_multibondIsingWeight_twisted ends D s J

/--
[hasDerivAt_multibondIsingPartition_twisted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionFiniteDisorderDerivative.lean)
-/
@[path]
private lemma hasDerivAt_multibondIsingPartition_twisted_eq
  [Fintype P]
  [DecidableEq P]
  {D : Finset P}
  {J : Real}
-- given
  (ends : P -> V × V) :
-- imply
  HasDerivAt (fun K => multibondIsingPartition ends (multibondTwistCoupling (fun _ => K) D)) (∑ s : V -> Bool, multibondIsingWeight ends (multibondTwistCoupling (fun _ => J) D) s * multibondTwistedBondSpin ends D s) J := by
-- proof
  apply StatMech.FrontierA.hasDerivAt_multibondIsingPartition_twisted ends D J

/--
[hasDerivAt_log_multibondIsingPartition_twisted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionFiniteDisorderDerivative.lean)
-/
@[path]
private lemma hasDerivAt_log_multibondIsingPartition_twisted_eq
  [Fintype P]
  [DecidableEq P]
  {D : Finset P}
  {J : Real}
-- given
  (ends : P -> V × V) :
-- imply
  HasDerivAt (fun K => Real.log (multibondIsingPartition ends (multibondTwistCoupling (fun _ => K) D))) (multibondMeanTwistedBondSpin ends D J) J := by
-- proof
  apply StatMech.FrontierA.hasDerivAt_log_multibondIsingPartition_twisted ends D J

/--
[hasDerivAt_multibondDisorderFreeEnergy_homogeneous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionFiniteDisorderDerivative.lean)
-/
@[path]
private lemma hasDerivAt_multibondDisorderFreeEnergy_homogeneous_eq
  [Fintype P]
  [DecidableEq P]
  {D : Finset P}
  {J : Real}
-- given
  (ends : P -> V × V) :
-- imply
  HasDerivAt (fun K => multibondDisorderFreeEnergy ends (fun _ => K) D) (multibondMeanTotalBondSpin ends J - multibondMeanTwistedBondSpin ends D J) J := by
-- proof
  apply StatMech.FrontierA.hasDerivAt_multibondDisorderFreeEnergy_homogeneous ends D J

/--
[hasDerivAt_finiteRectangularIsingDisorderFreeEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionFiniteDisorderDerivative.lean)
-/
@[path]
private lemma hasDerivAt_finiteRectangularIsingDisorderFreeEnergy_eq
  [Fintype P]
  [DecidableEq P]
  {m n : Nat}
  {J : Real} :
-- imply
  HasDerivAt (fun K => finiteRectangularIsingDisorderFreeEnergy K m n) (multibondMeanTotalBondSpin (cubicalDualEnds (a := m) (b := n) (c := max m n)) J - multibondMeanTwistedBondSpin (cubicalDualEnds (a := m) (b := n) (c := max m n)) (cubicalXYSheet (a := m) (b := n) (c := max m n) (0 : Fin (max m n + 1))) J) J := by
-- proof
  apply StatMech.FrontierA.hasDerivAt_finiteRectangularIsingDisorderFreeEnergy m n J


-- created on 2026-10-23

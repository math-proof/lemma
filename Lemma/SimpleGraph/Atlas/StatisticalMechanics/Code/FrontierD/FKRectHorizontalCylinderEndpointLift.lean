import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderEndpointLift.Part3
open SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectHorizontalCylinderUnexploredLiftSite_bottom_top_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderEndpointLift.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderUnexploredLiftSite_bottom_top_sub_eq
  {R : FKRectTorus}
  {rho : ConfigSpace (Sym2 R.Vertex)}
  {S : Finset (Fin R.width)}
  {source target : FKRectHorizontalCylinderUnexploredVertex R rho S}
  {sourceX targetX : Fin R.width}
-- given
  (hsource : source.1 = (sourceX, fkRectBottomRow R))
  (htarget : target.1 = (targetX, fkRectTopRow R)) :
-- imply
  let dx := (fkRectHorizontalCylinderUnexploredLiftPoint R rho S target).1 - (fkRectHorizontalCylinderUnexploredLiftPoint R rho S source).1 fkRectHorizontalCylinderUnexploredLiftSite R rho S target - fkRectHorizontalCylinderUnexploredLiftSite R rho S source = fkRectHorizontalCylinderSquareLiftedDisplacement dx R.height := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderUnexploredLiftSite_bottom_top_sub R rho S source target sourceX targetX hsource htarget

/--
[FKRectHorizontalCylinderUnexploredPlanarization.ofPairedWitness_embedding_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderEndpointLift.lean)
-/
@[path]
private lemma ofPairedWitness_embedding_sub_eq
  {R : FKRectTorus}
  {rho : ConfigSpace (Sym2 R.Vertex)}
  {S : Finset (Fin R.width)}
  {source target : FKRectHorizontalCylinderUnexploredVertex R rho S}
  {sourceX targetX : Fin R.width}
-- given
  (pair : Fin R.width -> Fin R.width)
  (hS : S.Nonempty)
  (hW : FKRectHorizontalCylinderDistinctPairedWitness R pair S rho)
  (hsource : source.1 = (sourceX, fkRectBottomRow R))
  (htarget : target.1 = (targetX, fkRectTopRow R)) :
-- imply
  let dx := (fkRectHorizontalCylinderUnexploredLiftPoint R rho S target).1 - (fkRectHorizontalCylinderUnexploredLiftPoint R rho S source).1 ((FKRectHorizontalCylinderUnexploredPlanarization.ofPairedWitness R rho pair S hS hW).embedding target).1 - ((FKRectHorizontalCylinderUnexploredPlanarization.ofPairedWitness R rho pair S hS hW).embedding source).1 = fkRectHorizontalCylinderSquareLiftedDisplacement dx R.height := by
-- proof
  apply StatMech.FrontierD.FKRectHorizontalCylinderUnexploredPlanarization.ofPairedWitness_embedding_sub R rho pair S hS hW source target sourceX targetX hsource htarget

/--
[fkRectHorizontalCylinderSquareLiftedDisplacement_coord_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderEndpointLift.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderSquareLiftedDisplacement_coord_sub_eq
  {R : FKRectTorus}
  {dx : Int} :
-- imply
  (fkRectHorizontalCylinderSquareLiftedDisplacement dx R.height) 0 - (fkRectHorizontalCylinderSquareLiftedDisplacement dx R.height) 1 = (R.height : Int) - 1 := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderSquareLiftedDisplacement_coord_sub R dx

/--
[fkRectHorizontalCylinder_oldDisplacement_parameter_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderEndpointLift.lean)
-/
@[path]
private lemma fkRectHorizontalCylinder_oldDisplacement_parameter_eq_eq
  {R : FKRectTorus}
  {rawDx oldDx : Int}
-- given
  (hbad : fkRectHorizontalCylinderSquareLiftedDisplacement rawDx R.height = fkRectHorizontalCylinderLiftedDisplacement oldDx R.height) :
-- imply
  oldDx = 2 * ((R.height : Int) - 1) := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinder_oldDisplacement_parameter_eq R rawDx oldDx hbad

/--
[fkRectHorizontalCylinder_not_oldDisplacement_of_width_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderEndpointLift.lean)
-/
@[path]
private lemma fkRectHorizontalCylinder_not_oldDisplacement_of_width_lt_eq
  {R : FKRectTorus}
  {rawDx : Int}
-- given
  (htall : R.width < 2 * (R.height - 1)) :
-- imply
  ¬ (∃ oldDx : Int, fkRectHorizontalCylinderSquareLiftedDisplacement rawDx R.height = fkRectHorizontalCylinderLiftedDisplacement oldDx R.height ∧ oldDx.natAbs <= R.width) := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinder_not_oldDisplacement_of_width_lt R rawDx htall

/--
[fkRectHorizontalCylinder_fixedEndpoint_sub_reflectedDiagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderEndpointLift.lean)
-/
@[path]
private lemma fkRectHorizontalCylinder_fixedEndpoint_sub_reflectedDiagonal_eq
  {R : FKRectTorus} :
-- imply
  fkRectHorizontalCylinderFixedEndpointDisplacement R.height - fkRectHorizontalCylinderReflectedDiagonalDisplacement R.height = ![0, 1] := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinder_fixedEndpoint_sub_reflectedDiagonal R

/--
[fkRectHorizontalCylinder_fixedEndpoint_add_correction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderEndpointLift.lean)
-/
@[path]
private lemma fkRectHorizontalCylinder_fixedEndpoint_add_correction_eq
  {R : FKRectTorus} :
-- imply
  fkRectHorizontalCylinderFixedEndpointDisplacement R.height + fkRectHorizontalCylinderFixedEndpointCorrection = fkRectHorizontalCylinderReflectedDiagonalDisplacement R.height := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinder_fixedEndpoint_add_correction R

/--
[fkQgt4CriticalFreeTwoPoint_reflectedDiagonal_eq_exact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderEndpointLift.lean)
-/
@[path]
private lemma fkQgt4CriticalFreeTwoPoint_reflectedDiagonal_eq_exact_eq
  {q : Real}
-- given
  (hq : 4 < q)
  (height : Nat) :
-- imply
  fkQgt4CriticalFreeTwoPoint hq (fkRectHorizontalCylinderReflectedDiagonalDisplacement height) = fkQgt4CriticalFreeExactDiagonalTwoPoint hq (height / 2) := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFreeTwoPoint_reflectedDiagonal_eq_exact hq height

/--
[fkQgt4CriticalFreeTwoPoint_fixedEndpoint_mul_correction_le_exact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderEndpointLift.lean)
-/
@[path]
private lemma fkQgt4CriticalFreeTwoPoint_fixedEndpoint_mul_correction_le_exact_eq
  {q : Real}
  {R : FKRectTorus}
-- given
  (hq : 4 < q) :
-- imply
  fkQgt4CriticalFreeTwoPoint hq (fkRectHorizontalCylinderFixedEndpointDisplacement R.height) * fkQgt4CriticalFreeTwoPoint hq fkRectHorizontalCylinderFixedEndpointCorrection <= fkQgt4CriticalFreeExactDiagonalTwoPoint hq (R.height / 2) := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFreeTwoPoint_fixedEndpoint_mul_correction_le_exact hq R

/--
[fkQgt4CriticalFreeTwoPoint_fixedEndpoint_le_exact_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderEndpointLift.lean)
-/
@[path]
private lemma fkQgt4CriticalFreeTwoPoint_fixedEndpoint_le_exact_div_eq
  {q : Real}
  {R : FKRectTorus}
-- given
  (hq : 4 < q) :
-- imply
  fkQgt4CriticalFreeTwoPoint hq (fkRectHorizontalCylinderFixedEndpointDisplacement R.height) <= fkQgt4CriticalFreeExactDiagonalTwoPoint hq (R.height / 2) / fkQgt4CriticalFreeTwoPoint hq fkRectHorizontalCylinderFixedEndpointCorrection := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFreeTwoPoint_fixedEndpoint_le_exact_div hq R

/--
[fkQgt4CriticalFreeTwoPoint_sq_le_exactDiagonal_of_coordSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderEndpointLift.lean)
-/
@[path]
private lemma fkQgt4CriticalFreeTwoPoint_sq_le_exactDiagonal_of_coordSub_eq
  {q : Real}
  {x : Site 2}
  {n : Nat}
-- given
  (hq : 4 < q)
  (hcoord : x 0 - x 1 = (n : Int)) :
-- imply
  fkQgt4CriticalFreeTwoPoint hq x ^ 2 <= fkQgt4CriticalFreeExactDiagonalTwoPoint hq n := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFreeTwoPoint_sq_le_exactDiagonal_of_coordSub hq x n hcoord

/--
[fkQgt4CriticalFreeTwoPoint_squareLiftedDisplacement_le_sqrt_exact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderEndpointLift.lean)
-/
@[path]
private lemma fkQgt4CriticalFreeTwoPoint_squareLiftedDisplacement_le_sqrt_exact_eq
  {q : Real}
  {R : FKRectTorus}
  {rawDx : Int}
-- given
  (hq : 4 < q) :
-- imply
  fkQgt4CriticalFreeTwoPoint hq (fkRectHorizontalCylinderSquareLiftedDisplacement rawDx R.height) <= Real.sqrt (fkQgt4CriticalFreeExactDiagonalTwoPoint hq (R.height - 1)) := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFreeTwoPoint_squareLiftedDisplacement_le_sqrt_exact hq R rawDx


-- created on 2026-10-23

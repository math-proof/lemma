import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingCutFiberReduction
open Finset SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectOpenGraph_forceHorizontalCutClosed_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingCutFiberReduction.lean)
-/
@[path]
private lemma fkRectOpenGraph_forceHorizontalCutClosed_le_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectOpenGraph R (fkRectForceHorizontalCutClosed R omega) ≤ fkRectOpenGraph R omega := by
-- proof
  apply StatMech.FrontierD.fkRectOpenGraph_forceHorizontalCutClosed_le R omega

/--
[fkRectBlackBoundaryCyclePrimalComponent_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingCutFiberReduction.lean)
-/
@[path]
private lemma fkRectBlackBoundaryCyclePrimalComponent_mk_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  fkRectBlackBoundaryCyclePrimalComponent R omega (Quot.mk _ d) = (fkRectOpenGraph R omega).connectedComponentMk (fkRectMedialDartPrimalLabel R d.1) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryCyclePrimalComponent_mk R omega d

/--
[fkRectHorizontalCutComponentTorusComponent_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingCutFiberReduction.lean)
-/
@[path]
private lemma fkRectHorizontalCutComponentTorusComponent_mk_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x : R.Vertex} :
-- imply
  fkRectHorizontalCutComponentTorusComponent R omega ((fkRectOpenGraph R (fkRectForceHorizontalCutClosed R omega)).connectedComponentMk x) = (fkRectOpenGraph R omega).connectedComponentMk x := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCutComponentTorusComponent_mk R omega x

/--
[sum_fkRectPrimalComponentBoundaryVerticalMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingCutFiberReduction.lean)
-/
@[path]
private lemma sum_fkRectPrimalComponentBoundaryVerticalMass_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  ∑ K : (fkRectOpenGraph R omega).ConnectedComponent, fkRectPrimalComponentBoundaryVerticalMass R omega K = ∑ C : FKRectConfigurationBlackBoundaryCycle R omega, (fkRectBlackBoundaryCycleWinding R omega C).2.natAbs := by
-- proof
  apply StatMech.FrontierD.sum_fkRectPrimalComponentBoundaryVerticalMass R omega

/--
[sum_fkRectPrimalComponentHorizontalCutCrossingCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingCutFiberReduction.lean)
-/
@[path]
private lemma sum_fkRectPrimalComponentHorizontalCutCrossingCount_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  ∑ K : (fkRectOpenGraph R omega).ConnectedComponent, fkRectPrimalComponentHorizontalCutCrossingCount R omega K = fkRectHorizontalCutPrimalCrossingClusterCount R (fkRectForceHorizontalCutClosed R omega) := by
-- proof
  apply StatMech.FrontierD.sum_fkRectPrimalComponentHorizontalCutCrossingCount R omega

/--
[fkRectUnorientedVerticalWindingTotal_le_two_mul_horizontalCut_of_fiberBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingCutFiberReduction.lean)
-/
@[path]
private lemma fkRectUnorientedVerticalWindingTotal_le_two_mul_horizontalCut_of_fiberBound_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
-- given
  (h : FKRectVerticalBoundaryMassCutFiberBound R omega) :
-- imply
  fkRectUnorientedVerticalWindingTotal R omega ≤ 2 * fkRectHorizontalCutPrimalCrossingClusterCount R (fkRectForceHorizontalCutClosed R omega) := by
-- proof
  apply StatMech.FrontierD.fkRectUnorientedVerticalWindingTotal_le_two_mul_horizontalCut_of_fiberBound R omega h

/--
[fkRectUnorientedVerticalWindingNumber_le_horizontalCut_of_fiberBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingCutFiberReduction.lean)
-/
@[path]
private lemma fkRectUnorientedVerticalWindingNumber_le_horizontalCut_of_fiberBound_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
-- given
  (h : FKRectVerticalBoundaryMassCutFiberBound R omega) :
-- imply
  fkRectUnorientedVerticalWindingNumber R omega ≤ fkRectHorizontalCutPrimalCrossingClusterCount R (fkRectForceHorizontalCutClosed R omega) := by
-- proof
  apply StatMech.FrontierD.fkRectUnorientedVerticalWindingNumber_le_horizontalCut_of_fiberBound R omega h

/--
[sum_fkRectPrimalComponentPositiveBoundaryVerticalMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingCutFiberReduction.lean)
-/
@[path]
private lemma sum_fkRectPrimalComponentPositiveBoundaryVerticalMass_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  ∑ K : (fkRectOpenGraph R omega).ConnectedComponent, fkRectPrimalComponentPositiveBoundaryVerticalMass R omega K = fkRectPositiveVerticalBoundaryWindingTotal R omega := by
-- proof
  apply StatMech.FrontierD.sum_fkRectPrimalComponentPositiveBoundaryVerticalMass R omega

/--
[fkRectUnorientedVerticalWindingNumber_le_horizontalCut_of_positiveFiberBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingCutFiberReduction.lean)
-/
@[path]
private lemma fkRectUnorientedVerticalWindingNumber_le_horizontalCut_of_positiveFiberBound_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
-- given
  (h : FKRectPositiveVerticalBoundaryCutFiberBound R omega) :
-- imply
  fkRectUnorientedVerticalWindingNumber R omega ≤ fkRectHorizontalCutPrimalCrossingClusterCount R (fkRectForceHorizontalCutClosed R omega) := by
-- proof
  apply StatMech.FrontierD.fkRectUnorientedVerticalWindingNumber_le_horizontalCut_of_positiveFiberBound R omega h

/--
[fkRectBlackBoundaryCycleWinding_eq_zero_of_componentHasNet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingCutFiberReduction.lean)
-/
@[path]
private lemma fkRectBlackBoundaryCycleWinding_eq_zero_of_componentHasNet_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {K : (fkRectOpenGraph R omega).ConnectedComponent}
  {C : FKRectConfigurationBlackBoundaryCycle R omega}
-- given
  (hnet : FKRectPrimalComponentHasNet R omega K)
  (hCK : fkRectBlackBoundaryCyclePrimalComponent R omega C = K) :
-- imply
  fkRectBlackBoundaryCycleWinding R omega C = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryCycleWinding_eq_zero_of_componentHasNet R omega K hnet C hCK

/--
[fkRectPrimalComponentPositiveBoundaryVerticalMass_eq_zero_of_hasNet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingCutFiberReduction.lean)
-/
@[path]
private lemma fkRectPrimalComponentPositiveBoundaryVerticalMass_eq_zero_of_hasNet_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {K : (fkRectOpenGraph R omega).ConnectedComponent}
-- given
  (hnet : FKRectPrimalComponentHasNet R omega K) :
-- imply
  fkRectPrimalComponentPositiveBoundaryVerticalMass R omega K = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalComponentPositiveBoundaryVerticalMass_eq_zero_of_hasNet R omega K hnet

/--
[fkRectPositiveVerticalBoundaryCutFiberBound_of_componentHasNet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingCutFiberReduction.lean)
-/
@[path]
private lemma fkRectPositiveVerticalBoundaryCutFiberBound_of_componentHasNet_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {K : (fkRectOpenGraph R omega).ConnectedComponent}
-- given
  (hnet : FKRectPrimalComponentHasNet R omega K) :
-- imply
  fkRectPrimalComponentPositiveBoundaryVerticalMass R omega K ≤ fkRectPrimalComponentHorizontalCutCrossingCount R omega K := by
-- proof
  apply StatMech.FrontierD.fkRectPositiveVerticalBoundaryCutFiberBound_of_componentHasNet R omega K hnet


-- created on 2026-10-23

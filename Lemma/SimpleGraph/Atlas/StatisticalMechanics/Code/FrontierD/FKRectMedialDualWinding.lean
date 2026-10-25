import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialDualWinding
open StatMech StatMech.FrontierD


/--
[fkRectMedialDualShiftColumnEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialDualWinding.lean)
-/
@[path]
private lemma fkRectMedialDualShiftColumnEquiv_apply_eq
  {R : FKRectTorus}
  {i : Fin R.medialTorus.width} :
-- imply
  fkRectMedialDualShiftColumnEquiv R i = SixVertexArrows.cyclicPred R.medialTorus.width_pos i := by
-- proof
  apply StatMech.FrontierD.fkRectMedialDualShiftColumnEquiv_apply R i

/--
[fkRectMedialDualShiftDart_verticalSeam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialDualWinding.lean)
-/
@[path]
private lemma fkRectMedialDualShiftDart_verticalSeam_eq
  {R : FKRectTorus}
  {i : Fin R.medialTorus.width} :
-- imply
  fkRectMedialDualShiftDart R (fkMedialVerticalSeamDart R.medialTorus i) = fkMedialVerticalSeamDart R.medialTorus (fkRectMedialDualShiftColumnEquiv R i) := by
-- proof
  apply StatMech.FrontierD.fkRectMedialDualShiftDart_verticalSeam R i

/--
[fkMedialCanonicalVerticalSeamSign_dualShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialDualWinding.lean)
-/
@[path]
private lemma fkMedialCanonicalVerticalSeamSign_dualShift_eq
  {R : FKRectTorus}
  {i : Fin R.medialTorus.width} :
-- imply
  fkMedialCanonicalVerticalSeamSign R.medialTorus (fkRectMedialDualShiftColumnEquiv R i) = -fkMedialCanonicalVerticalSeamSign R.medialTorus i := by
-- proof
  apply StatMech.FrontierD.fkMedialCanonicalVerticalSeamSign_dualShift R i

/--
[fkMedialLoopCanonicalVerticalFlux_dualShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialDualWinding.lean)
-/
@[path]
private lemma fkMedialLoopCanonicalVerticalFlux_dualShift_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKMedialLoop R.medialTorus (fkRectConfigurationToMedialPairing R omega)} :
-- imply
  fkMedialLoopCanonicalVerticalFlux (fkRectConfigurationToMedialPairing R (fkRectDualConfigurationEquiv R omega)) ((fkRectMedialDualShiftGraphIso R omega).connectedComponentEquiv C) = -fkMedialLoopCanonicalVerticalFlux (fkRectConfigurationToMedialPairing R omega) C := by
-- proof
  apply StatMech.FrontierD.fkMedialLoopCanonicalVerticalFlux_dualShift R omega C

/--
[fkRectUnorientedVerticalWindingTotal_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialDualWinding.lean)
-/
@[path]
private lemma fkRectUnorientedVerticalWindingTotal_dual_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectUnorientedVerticalWindingTotal R (fkRectDualConfigurationEquiv R omega) = fkRectUnorientedVerticalWindingTotal R omega := by
-- proof
  apply StatMech.FrontierD.fkRectUnorientedVerticalWindingTotal_dual R omega

/--
[fkRectUnorientedVerticalWindingNumber_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialDualWinding.lean)
-/
@[path]
private lemma fkRectUnorientedVerticalWindingNumber_dual_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectUnorientedVerticalWindingNumber R (fkRectDualConfigurationEquiv R omega) = fkRectUnorientedVerticalWindingNumber R omega := by
-- proof
  apply StatMech.FrontierD.fkRectUnorientedVerticalWindingNumber_dual R omega


-- created on 2026-10-23

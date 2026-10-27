import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.StatisticalMechanics.Code.FrontierD.FKRectMedialDualShift.Part3
open StatMech StatMech.FrontierD


/--
[fkRectMedialDualUnshiftVertex_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialDualShift.lean)
-/
@[path]
private lemma fkRectMedialDualUnshiftVertex_shift_eq
  {R : FKRectTorus}
  {v : R.medialTorus.Vertex} :
-- imply
  fkRectMedialDualUnshiftVertex R (fkRectMedialDualShiftVertex R v) = v := by
-- proof
  apply StatMech.FrontierD.fkRectMedialDualUnshiftVertex_shift R v

/--
[fkRectMedialDualShiftVertex_unshift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialDualShift.lean)
-/
@[path]
private lemma fkRectMedialDualShiftVertex_unshift_eq
  {R : FKRectTorus}
  {v : R.medialTorus.Vertex} :
-- imply
  fkRectMedialDualShiftVertex R (fkRectMedialDualUnshiftVertex R v) = v := by
-- proof
  apply StatMech.FrontierD.fkRectMedialDualShiftVertex_unshift R v

/--
[fkRectMedialDualUnshiftDart_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialDualShift.lean)
-/
@[path]
private lemma fkRectMedialDualUnshiftDart_shift_eq
  {R : FKRectTorus}
  {d : FKMedialDart R.medialTorus} :
-- imply
  fkRectMedialDualUnshiftDart R (fkRectMedialDualShiftDart R d) = d := by
-- proof
  apply StatMech.FrontierD.fkRectMedialDualUnshiftDart_shift R d

/--
[fkRectMedialDualShiftDart_unshift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialDualShift.lean)
-/
@[path]
private lemma fkRectMedialDualShiftDart_unshift_eq
  {R : FKRectTorus}
  {d : FKMedialDart R.medialTorus} :
-- imply
  fkRectMedialDualShiftDart R (fkRectMedialDualUnshiftDart R d) = d := by
-- proof
  apply StatMech.FrontierD.fkRectMedialDualShiftDart_unshift R d

/--
[fkRectTorusMedialEdgeEquiv_dualShiftVertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialDualShift.lean)
-/
@[path]
private lemma fkRectTorusMedialEdgeEquiv_dualShiftVertex_eq
  {R : FKRectTorus}
  {v : R.medialTorus.Vertex} :
-- imply
  fkRectTorusMedialEdgeEquiv R (fkRectMedialDualShiftVertex R v) = fkRectEdgeToDualEdge R (fkRectTorusMedialEdgeEquiv R v) := by
-- proof
  apply StatMech.FrontierD.fkRectTorusMedialEdgeEquiv_dualShiftVertex R v

/--
[fkRectClosedPairingAtEdge_edgeToDualEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialDualShift.lean)
-/
@[path]
private lemma fkRectClosedPairingAtEdge_edgeToDualEdge_eq
  {R : FKRectTorus}
  {e : R.EdgeIndex} :
-- imply
  fkRectClosedPairingAtEdge (fkRectEdgeToDualEdge R e) = !(fkRectClosedPairingAtEdge e) := by
-- proof
  apply StatMech.FrontierD.fkRectClosedPairingAtEdge_edgeToDualEdge R e

/--
[fkRectConfigurationToMedialPairing_dual_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialDualShift.lean)
-/
@[path]
private lemma fkRectConfigurationToMedialPairing_dual_shift_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {v : R.medialTorus.Vertex} :
-- imply
  fkRectConfigurationToMedialPairing R (fkRectDualConfigurationEquiv R omega) (fkRectMedialDualShiftVertex R v) = fkRectConfigurationToMedialPairing R omega v := by
-- proof
  apply StatMech.FrontierD.fkRectConfigurationToMedialPairing_dual_shift R omega v

/--
[fkRectMedialDualShiftDart_localMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialDualShift.lean)
-/
@[path]
private lemma fkRectMedialDualShiftDart_localMate_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialDart R.medialTorus} :
-- imply
  fkRectMedialDualShiftDart R (fkMedialLocalMate (fkRectConfigurationToMedialPairing R omega) d) = fkMedialLocalMate (fkRectConfigurationToMedialPairing R (fkRectDualConfigurationEquiv R omega)) (fkRectMedialDualShiftDart R d) := by
-- proof
  apply StatMech.FrontierD.fkRectMedialDualShiftDart_localMate R omega d

/--
[fkRectMedialDualShiftDart_bondMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialDualShift.lean)
-/
@[path]
private lemma fkRectMedialDualShiftDart_bondMate_eq
  {R : FKRectTorus}
  {d : FKMedialDart R.medialTorus} :
-- imply
  fkRectMedialDualShiftDart R (fkMedialBondMate R.medialTorus d) = fkMedialBondMate R.medialTorus (fkRectMedialDualShiftDart R d) := by
-- proof
  apply StatMech.FrontierD.fkRectMedialDualShiftDart_bondMate R d

/--
[fkRectMedialDualShiftDart_boundaryStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialDualShift.lean)
-/
@[path]
private lemma fkRectMedialDualShiftDart_boundaryStep_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialDart R.medialTorus} :
-- imply
  fkRectMedialDualShiftDart R (fkMedialBoundaryStep (fkRectConfigurationToMedialPairing R omega) d) = fkMedialBoundaryStep (fkRectConfigurationToMedialPairing R (fkRectDualConfigurationEquiv R omega)) (fkRectMedialDualShiftDart R d) := by
-- proof
  apply StatMech.FrontierD.fkRectMedialDualShiftDart_boundaryStep R omega d

/--
[fkRectMedialDualShiftDart_boundaryStep_iterate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialDualShift.lean)
-/
@[path]
private lemma fkRectMedialDualShiftDart_boundaryStep_iterate_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialDart R.medialTorus}
  {n : Nat} :
-- imply
  fkRectMedialDualShiftDart R ((fkMedialBoundaryStep (fkRectConfigurationToMedialPairing R omega))^[n] d) = (fkMedialBoundaryStep (fkRectConfigurationToMedialPairing R (fkRectDualConfigurationEquiv R omega)))^[n] (fkRectMedialDualShiftDart R d) := by
-- proof
  apply StatMech.FrontierD.fkRectMedialDualShiftDart_boundaryStep_iterate R omega d n


-- created on 2026-10-23

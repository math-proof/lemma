import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicEndpointRadialShellCardinality
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm


/--
[vertexEndpointRadialShell_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointRadialShellCardinality.lean)
-/
@[path]
private lemma vertexEndpointRadialShell_lt_eq
  {n : Nat} :
-- imply
  forall z, vertexEndpointRadialShell n z < 3 * n + 1 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexEndpointRadialShell_lt n

/--
[vertexEndpointRadialShellCode_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointRadialShellCardinality.lean)
-/
@[path]
private lemma vertexEndpointRadialShellCode_injective_eq
  {n r : Nat}
  {z w : Option (FKIsingSquareFullVertexNode n)}
-- given
  (hz : vertexEndpointRadialShell n z = r)
  (hw : vertexEndpointRadialShell n w = r)
  (hcode : vertexEndpointRadialShellCode n r z hz = vertexEndpointRadialShellCode n r w hw) :
-- imply
  z = w := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexEndpointRadialShellCode_injective n r hz hw hcode

/--
[vertexEndpointRadialShell_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointRadialShellCardinality.lean)
-/
@[path]
private lemma vertexEndpointRadialShell_card_le_eq
  {n r : Nat} :
-- imply
  (Finset.univ.filter (fun z : Option (FKIsingSquareFullVertexNode n) => vertexEndpointRadialShell n z = r)).card <= 3 * (r + 1) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexEndpointRadialShell_card_le n r

/--
[faceEndpointRadialShell_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointRadialShellCardinality.lean)
-/
@[path]
private lemma faceEndpointRadialShell_lt_eq
  {n : Nat} :
-- imply
  forall z, faceEndpointRadialShell n z < 3 * n + 1 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceEndpointRadialShell_lt n

/--
[faceEndpointRadialShellCode_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointRadialShellCardinality.lean)
-/
@[path]
private lemma faceEndpointRadialShellCode_injective_eq
  {n r : Nat}
  {z w : Option (FKIsingSquareFullFaceNode n)}
-- given
  (hz : faceEndpointRadialShell n z = r)
  (hw : faceEndpointRadialShell n w = r)
  (hcode : faceEndpointRadialShellCode n r z hz = faceEndpointRadialShellCode n r w hw) :
-- imply
  z = w := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceEndpointRadialShellCode_injective n r hz hw hcode

/--
[faceEndpointRadialShell_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointRadialShellCardinality.lean)
-/
@[path]
private lemma faceEndpointRadialShell_card_le_eq
  {n r : Nat} :
-- imply
  (Finset.univ.filter (fun z : Option (FKIsingSquareFullFaceNode n) => faceEndpointRadialShell n z = r)).card <= 3 * (r + 1) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceEndpointRadialShell_card_le n r

/--
[vertexSpatialTargetResidualPotential_le_endpointRadialHarmonic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointRadialShellCardinality.lean)
-/
@[path]
private lemma vertexSpatialTargetResidualPotential_le_endpointRadialHarmonic_eq
  {n : Nat}
  {x : Option (FKIsingSquareFullVertexNode n)}
  {C : Real}
-- given
  (hn : 0 < n)
  (target : Option (FKIsingSquareFullVertexNode n) -> Real)
  (hC : 0 <= C)
  (hpoint : forall z, vertexSpatialTargetResidual n target z * vertexPointPoissonBarrier n z x <= C / ((n : Real) * ((vertexEndpointRadialShell n z + 1 : Nat) : Real) ^ 2)) :
-- imply
  vertexSpatialTargetResidualPotential n target x <= C * 3 * (harmonic (3 * n + 1) : Real) / (n : Real) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexSpatialTargetResidualPotential_le_endpointRadialHarmonic n hn target x C hC hpoint

/--
[faceSpatialTargetResidualPotential_le_endpointRadialHarmonic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointRadialShellCardinality.lean)
-/
@[path]
private lemma faceSpatialTargetResidualPotential_le_endpointRadialHarmonic_eq
  {n : Nat}
  {x : Option (FKIsingSquareFullFaceNode n)}
  {C : Real}
-- given
  (hn : 0 < n)
  (target : Option (FKIsingSquareFullFaceNode n) -> Real)
  (hC : 0 <= C)
  (hpoint : forall z, faceSpatialTargetResidual n target z * facePointPoissonBarrier n z x <= C / ((n : Real) * ((faceEndpointRadialShell n z + 1 : Nat) : Real) ^ 2)) :
-- imply
  faceSpatialTargetResidualPotential n target x <= C * 3 * (harmonic (3 * n + 1) : Real) / (n : Real) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceSpatialTargetResidualPotential_le_endpointRadialHarmonic n hn target x C hC hpoint

/--
[tendsto_endpointRadialHarmonic_div_natCast_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointRadialShellCardinality.lean)
-/
@[path]
private lemma tendsto_endpointRadialHarmonic_div_natCast_succ_eq :
-- imply
  Filter.Tendsto (fun n : Nat => (harmonic (3 * (n + 1) + 1) : Real) / ((n + 1 : Nat) : Real)) Filter.atTop (nhds 0) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.tendsto_endpointRadialHarmonic_div_natCast_succ


-- created on 2026-10-23

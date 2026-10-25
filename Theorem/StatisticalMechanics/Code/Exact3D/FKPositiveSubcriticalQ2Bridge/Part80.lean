/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteIsingFKBridge.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.SurfaceTensionConvexity
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Theorem.StatisticalMechanics.Code.FK.RotationInvariance.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.SimonLiebFull.Part2
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part82
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteSubcaseAbsorption_of_boundaryVertexDecrementedSourceAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteSubcaseAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH v hv Ω
  exact
    (finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSubcase_sum_le_vertexCutoffSum
      (β := β) (H := H) (le_of_lt hβpos) (le_of_lt hH) Ω).trans
      (hn H hH (Ω.image Sigma.fst) v hv)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteLabelCaseAbsorption_of_boundaryVertexSigmaFiniteSubcaseAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteSubcaseAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteLabelCaseAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH v hv Ω
  refine
    ⟨1, (fun _ => (0 : Fin 1)),
      (fun _ => finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v),
      ?_, ?_⟩
  · intro i
    have hi : i = (0 : Fin 1) := Subsingleton.elim i 0
    subst i
    simpa using hn H hH v hv Ω
  · simp


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteSubcaseAbsorption_of_boundaryVertexSigmaFiniteLabelCaseAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteLabelCaseAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteSubcaseAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH v hv Ω
  rcases hn H hH v hv Ω with ⟨k, label, A, hcase, hbudget⟩
  exact
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSubcase_sum_le_of_label_sum_le
      (β := β) (H := H) (n := n) (v := v) Ω label hcase hbudget


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteLabelCaseAbsorption_of_boundaryVertexDecrementedSourceAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteLabelCaseAbsorptionPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteLabelCaseAbsorption_of_boundaryVertexSigmaFiniteSubcaseAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteSubcaseAbsorption_of_boundaryVertexDecrementedSourceAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorption_of_boundaryVertexSigmaFiniteSubcaseAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteSubcaseAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  rw [←
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport_sum_eq_vertexCutoffSum
      β H n Ω v]
  exact
    hn H hH v hv
      (finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport
        n Ω v)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorption_of_boundaryVertexSigmaFiniteSubcaseAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteSubcaseAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorptionPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorption_of_boundaryVertexDecrementedSourceAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorption_of_boundaryVertexSigmaFiniteSubcaseAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorption_of_boundaryVertexSigmaFiniteLabelCaseAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteLabelCaseAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorptionPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorption_of_boundaryVertexSigmaFiniteSubcaseAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteSubcaseAbsorption_of_boundaryVertexSigmaFiniteLabelCaseAbsorption
      h)


end Exact3D
end StatMech

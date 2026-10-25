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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part98
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositiveSupportCurrentWitness_of_originalPathWitness3D
    (hpath : FiniteBoundaryGhostOriginalPathWitness3D) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositiveSupportCurrentWitnessPositiveSubcritical := by
  intro β _hβpos _hβc
  filter_upwards [hpath] with n hn
  intro H _hH v hv
  rcases hn v hv with ⟨p, hinside⟩
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J :=
    Sharpness.couplingIn
      (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
      (finiteBoundaryGhostOriginalSet 3 n)
  let m : ↥G.edgeFinset → ℕ := fun e => p.1.edges.count e.1
  refine ⟨m, ?_, ?_⟩
  · have hvbdry : FK.boxBoundary 3 n v := (Finset.mem_filter.mp hv).2
    have hne : some (IsingFK.boxOrigin 3 n) ≠ some v := by
      intro hsome
      exact boxOrigin_ne_of_boxBoundary 3 n hvbdry (Option.some.inj hsome)
    simpa [G, m] using sources_ofEdgeFun_path_count G p hne
  · intro e hepos
    dsimp [m] at hepos
    exact finiteBoundaryGhostLocalizedCoupling_pos_of_edgeInside 3 n H
      (hinside e hepos)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositiveCurrentWitness_of_boundaryVertexDenominatorPositiveSupportCurrentWitness
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositiveSupportCurrentWitnessPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositiveCurrentWitnessPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH v hv
  rcases hn H hH v hv with ⟨m, hsrc, hsupport⟩
  refine ⟨m, hsrc, ?_⟩
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J :=
    Sharpness.couplingIn
      (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
      (finiteBoundaryGhostOriginalSet 3 n)
  exact
    weight_ofEdgeFun_pos_of_pos_on_support G β J hβpos m hsupport


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositive_of_boundaryVertexDenominatorPositiveCurrentWitness
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositiveCurrentWitnessPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositivePositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH v hv
  rcases hn H hH v hv with ⟨m, hsrc, hweight⟩
  exact
    finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct_pos_of_boundary_current_witness
      (β := β) (H := H) (n := n) hβpos hH v hv m hsrc hweight


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositive_of_boundaryVertexDenominatorPositiveSupportCurrentWitness
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositiveSupportCurrentWitnessPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositivePositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositive_of_boundaryVertexDenominatorPositiveCurrentWitness
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositiveCurrentWitness_of_boundaryVertexDenominatorPositiveSupportCurrentWitness
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositive_of_originalPathWitness3D
    (hpath : FiniteBoundaryGhostOriginalPathWitness3D) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositivePositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositive_of_boundaryVertexDenominatorPositiveSupportCurrentWitness
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositiveSupportCurrentWitness_of_originalPathWitness3D
      hpath)


end Exact3D
end StatMech

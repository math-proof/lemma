/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part103
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternOwnerPairShareAtEdgeResidualBranchSixthFiniteSumBoundsAt_of_strictMismatchOwnerPairShareAtEdgeResidualBranchSixthFiniteSumBoundsAt
    {β : ℝ} {n : ℕ}
    (hbounds :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternStrictMismatchOwnerPairShareAtEdgeResidualBranchSixthFiniteSumBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternOwnerPairShareAtEdgeResidualBranchSixthFiniteSumBoundsAt
      β n := by
  intro v hvwedge hlt hypos
  classical
  dsimp only at hbounds ⊢
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let supportPatterns : Finset (Finset Edge) :=
    Finset.filter (fun S => S.Nonempty)
      (Finset.powerset (doubledBoxOriginIncidentEdges n))
  rcases hbounds v hvwedge hlt hypos e0 hedge Ω with
    ⟨hemptyStrict, hinnerStrict⟩
  constructor
  · intro S hS ew hew
    have hS' :
        S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
          (fun S => S.Nonempty) := by
      simpa [supportPatterns] using hS
    have hmis : ew ≠ e0 :=
      doubledBoxOriginIncidentSupportPattern_edge_ne_selectedEdge_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) hedge hS' hew
    simpa [Ωactive, supportPatterns, w] using
      hemptyStrict S (by simpa [supportPatterns] using hS) ew hew hmis
  · intro S hS ew hew
    have hS' :
        S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
          (fun S => S.Nonempty) := by
      simpa [supportPatterns] using hS
    have hmis : ew ≠ e0 :=
      doubledBoxOriginIncidentSupportPattern_edge_ne_selectedEdge_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) hedge hS' hew
    simpa [Ωactive, supportPatterns, w] using
      hinnerStrict S (by simpa [supportPatterns] using hS) ew hew hmis

end Exact3D
end StatMech

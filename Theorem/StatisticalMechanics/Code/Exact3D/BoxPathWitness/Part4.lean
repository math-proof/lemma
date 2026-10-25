/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoxPathWitness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
import Def.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part3
open Filter


namespace StatMech

namespace Exact3D

open StatMech.Lattice


theorem finiteBoundaryGhostOriginalPathWitness_of_boxPath
    {n : ℕ} {a b : FK.boxVerts 3 n}
    (p0 : (FK.boxGraph 3 n).Path a b) :
    ∃ p :
      (Sharpness.withGhost (FK.boxGraph 3 n)).Path (some a) (some b),
      ∀ e : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset,
        0 < p.1.edges.count e.1 →
          Sharpness.edgeInside (finiteBoundaryGhostOriginalSet 3 n) e.1 := by
  classical
  let f := boxGraphSomeHom 3 n
  let p : (Sharpness.withGhost (FK.boxGraph 3 n)).Path (some a) (some b) :=
    SimpleGraph.Path.map f (Option.some_injective (FK.boxVerts 3 n)) p0
  refine ⟨p, ?_⟩
  intro e hepos
  have hemem : e.1 ∈ p.1.edges := List.count_pos_iff.mp hepos
  change e.1 ∈ (p0.1.map f).edges at hemem
  rw [SimpleGraph.Walk.edges_map] at hemem
  rcases List.mem_map.mp hemem with ⟨e0, _he0, heq⟩
  rw [← heq]
  simpa [f, boxGraphSomeHom] using
    finiteBoundaryGhostOriginalSet_edgeInside_map_some 3 n e0


theorem finiteBoundaryGhostOriginalPathWitness3D :
    FiniteBoundaryGhostOriginalPathWitness3D := by
  filter_upwards [] with n
  intro v _hv
  have hreach :
      (FK.boxGraph 3 n).Reachable (IsingFK.boxOrigin 3 n) v :=
    boxGraph_reachable 3 n (IsingFK.boxOrigin 3 n) v
  rcases hreach.exists_isPath with ⟨w, hw⟩
  exact finiteBoundaryGhostOriginalPathWitness_of_boxPath ⟨w, hw⟩


theorem finiteQ2BoundaryVertexDenominatorPositiveSupportCurrentWitness_from_boxGeometry :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositiveSupportCurrentWitnessPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositiveSupportCurrentWitness_of_originalPathWitness3D
    finiteBoundaryGhostOriginalPathWitness3D


theorem finiteQ2BoundaryVertexDenominatorPositive_from_boxGeometry :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositivePositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositive_of_originalPathWitness3D
    finiteBoundaryGhostOriginalPathWitness3D


theorem
    finiteQ2PositiveDenominatorComponentSumAbsorption_of_boxGeometry_componentSumAbsorption
    (hsum :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentSumAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorptionPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption_of_originalPathWitness3D_componentSumAbsorption
    finiteBoundaryGhostOriginalPathWitness3D
    hsum

end Exact3D
end StatMech

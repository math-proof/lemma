/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWGapSymmetry.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalTraceContact
import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalSelectionObstruction
import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
import Theorem.StatisticalMechanics.Code.FK.WeightedParameterMonotoneClosed
import Theorem.StatisticalMechanics.Code.FrontierD.FKBoundarySingleMerge
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part41
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorVertexToCollared_injective {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Function.Injective (rlc_connectorVertexToCollared gamma gamma') := by
  intro x y hxy
  apply Subtype.ext
  exact congrArg
    (fun z : RlcConnectorCollaredVertex gamma gamma' => z.1) hxy


theorem rlc_extremalSelection_badCollar_inside_not_augmented :
    (rlc_connectorCollaredWallGraph
      rlc_traceSplitCounterexampleRight
      rlc_traceSplitCounterexampleLeft).Adj
        (rlc_connectorVertexToCollared
          rlc_traceSplitCounterexampleRight
          rlc_traceSplitCounterexampleLeft
          rlc_extremalSelectionBadCollarX)
        (rlc_connectorVertexToCollared
          rlc_traceSplitCounterexampleRight
          rlc_traceSplitCounterexampleLeft
          rlc_extremalSelectionBadCollarY) ∧
      ¬(rlc_connectorAugmentedPlanarDomain
        rlc_traceSplitCounterexampleRight
        rlc_traceSplitCounterexampleLeft).G.Adj
          rlc_extremalSelectionBadCollarX
          rlc_extremalSelectionBadCollarY := by
  have hwall : s((![-2, -1] : Site 2), ![-2, 0]) ∈
      rlc_connectorCollaredWallEdges
        rlc_traceSplitCounterexampleRight
        rlc_traceSplitCounterexampleLeft := by
    rw [rlc_connectorCollaredWallEdges]
    apply Finset.mem_union_right
    apply rlc_pimsEdgeEquiv_mem_connectorPIMSExteriorPreimages
      rlc_traceSplitCounterexampleRight
      rlc_traceSplitCounterexampleLeft
      rlc_extremalSelection_bad_target_mem_connectorEdges
    · exact rlc_extremalSelection_bad_source_not_connectorEdges
    · exact rlc_extremalSelection_bad_source_not_traceEdges
  constructor
  · refine ⟨?_, ?_⟩
    · simp [rlc_connectorVertexToCollared,
        rlc_extremalSelectionBadCollarX,
        rlc_extremalSelectionBadCollarY,
        hypercubicLattice_adj, Fin.sum_univ_two]
    · simpa [rlc_connectorVertexToCollared,
        rlc_extremalSelectionBadCollarX,
        rlc_extremalSelectionBadCollarY] using hwall
  · rintro (hfinite | htrace)
    · exact rlc_extremalSelection_bad_source_not_connectorEdges
        (by simpa [rlc_extremalSelectionBadCollarX,
          rlc_extremalSelectionBadCollarY] using hfinite.2)
    · exact rlc_extremalSelection_bad_source_not_traceEdges
        (by simpa [rlc_extremalSelectionBadCollarX,
          rlc_extremalSelectionBadCollarY] using htrace.2)


theorem rlc_connectorAugmented_adj_collared {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {x y : RlcConnectorVertex n}
    (hxy : (rlc_connectorAugmentedPlanarDomain gamma gamma').G.Adj x y) :
    (rlc_connectorCollaredPlanarDomain gamma gamma').G.Adj
      (rlc_connectorVertexToCollared gamma gamma' x)
      (rlc_connectorVertexToCollared gamma gamma' y) := by
  refine ⟨(rlc_connectorAugmentedPlanarDomain gamma gamma').isSub hxy, ?_⟩
  rw [rlc_connectorCollaredWallEdges]
  apply Finset.mem_union_left
  rw [Finset.mem_union]
  rcases hxy with hfinite | htrace
  · exact Or.inl hfinite.2
  · exact Or.inr htrace.2


end
end StatMech.Universality

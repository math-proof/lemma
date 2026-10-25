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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part48
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorOuterRestrictedZ_eq {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) :
    rlc_connectorOuterRestrictedZ gamma gamma' p q =
      p ^ (rlc_connectorOuterSpokeGraph gamma gamma').edgeFinset.card *
        rlc_connectorForcedDualZ gamma gamma' p q := by
  unfold rlc_connectorOuterRestrictedZ rlc_connectorForcedDualZ
  simp_rw [rlc_connectorOuter_bcWeight_eq_pfdDualWeight]
  rw [Finset.mul_sum]


theorem rlc_connectorOuterRestrictedProb_eq_forcedDualProb {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {p q : Real} (hp : 0 < p) :
    rlc_connectorOuterRestrictedProb gamma gamma' p q tau =
      rlc_connectorForcedDualProb gamma gamma' p q tau := by
  unfold rlc_connectorOuterRestrictedProb rlc_connectorForcedDualProb
  rw [rlc_connectorOuter_bcWeight_eq_pfdDualWeight,
    rlc_connectorOuterRestrictedZ_eq]
  exact mul_div_mul_left _ _ (pow_ne_zero _ hp.ne')

theorem rlc_connector_path_end_mem_vertices {a b c d : Int}
    (gamma : RlcCrossingPath a b c d) :
    (gamma.2.1 : Site 2) ∈ rlc_pathVertices gamma := by
  simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
  exact ⟨⟨gamma.2.1, rightSide_subset gamma.2.1.2⟩,
    gamma.2.2.1.end_mem_support, rfl⟩


end
end StatMech.Universality

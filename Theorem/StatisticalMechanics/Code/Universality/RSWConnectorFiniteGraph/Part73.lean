module
public import Theorem.StatisticalMechanics.Code.Universality.RSWGapSymmetry.Part4
public import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalTraceContact
public import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalSelectionObstruction
public import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
public import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
public import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
public import Theorem.StatisticalMechanics.Code.FK.WeightedParameterMonotoneClosed
public import Theorem.StatisticalMechanics.Code.FrontierD.FKBoundarySingleMerge
public import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
public import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part95
open Finset SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorPIMSSourceOpenCase_not_trace {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {e : Sym2 (Site 2)}
    (hcase : RlcConnectorPIMSSourceOpenCase gamma gamma' tau e) :
    rlc_pimsEdgeEquiv e ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
  rcases hcase with ⟨hsource, _⟩ | ⟨_, htrace⟩
  · intro he
    rcases Finset.mem_union.mp he with hright | hleft
    · exact Finset.disjoint_left.mp
        (rlc_rightPathEdges_disjoint_connector gamma gamma')
          hright hsource
    · exact Finset.disjoint_left.mp
        (rlc_leftPathEdges_disjoint_connector gamma gamma')
          hleft hsource
  · exact htrace


theorem rlc_connectorPIMSSourceOpenCase_of_maskedDual_open {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : Sym2 (Site 2))
    (hnotTrace : rlc_pimsEdgeEquiv e ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1)
    (hopen : rlc_dualReflectConfig
      (rlc_maskConfig (rlc_connectorEdges gamma gamma')
        (rlc_connectorAmbientMixedConfig gamma gamma' tau)) e = true) :
    RlcConnectorPIMSSourceOpenCase gamma gamma' tau e := by
  rw [rlc_dualReflectConfig_eq_pims] at hopen
  by_cases hsource : rlc_pimsEdgeEquiv e ∈
      rlc_connectorEdges gamma gamma'
  · left
    refine ⟨hsource, ?_⟩
    simpa [rlc_maskConfig, hsource] using hopen
  · exact Or.inr ⟨hsource, hnotTrace⟩


theorem rlc_connectorPIMSReflectedConfig_open_of_sourceOpenCase {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : Sym2 (Site 2))
    (htarget : e ∈ rlc_connectorEdges gamma gamma')
    (hcase : RlcConnectorPIMSSourceOpenCase gamma gamma' tau e) :
    rlc_connectorPIMSReflectedConfig gamma gamma' tau
      (rlc_connectorEdgeLift gamma gamma' e htarget) = true := by
  rw [rlc_connectorPIMSReflectedConfig_apply,
    rlc_connectorEdgeLift_map]
  rcases hcase with ⟨hsource, hclosed⟩ | ⟨hsource, htrace⟩
  · rw [rlc_connectorAmbientMixedConfig_connectorEdge
      gamma gamma' tau hsource, hclosed]
    rfl
  · simp [rlc_connectorAmbientMixedConfig, hsource, htrace]


end
end StatMech.Universality

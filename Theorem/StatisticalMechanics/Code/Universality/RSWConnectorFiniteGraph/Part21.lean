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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part28
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_openSub_PIMSVariableConfig {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.openSub (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorPIMSVariableConfig gamma gamma' rho) =
      FK.openSub (rlc_connectorPIMSVariableGraph gamma gamma') rho := by
  ext x y
  rw [FK.openSub_adj, FK.openSub_adj]
  by_cases hvar : (rlc_connectorPIMSVariableGraph gamma gamma').Adj x y
  · simp [rlc_connectorPIMSVariableConfig, SimpleGraph.mem_edgeSet,
      hvar, hvar.1]
  · simp [rlc_connectorPIMSVariableConfig, SimpleGraph.mem_edgeSet, hvar]


theorem rlc_openSub_PIMSAssembleConfig {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.openSub (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorPIMSAssembleConfig gamma gamma' rho) =
      FK.openSub (rlc_connectorPIMSVariableGraph gamma gamma') rho ⊔
        rlc_connectorPIMSExteriorGraph gamma gamma' := by
  ext x y
  rw [FK.openSub_adj, SimpleGraph.sup_adj, FK.openSub_adj]
  by_cases hvar : (rlc_connectorPIMSVariableGraph gamma gamma').Adj x y
  · have hnotext :
        ¬ (rlc_connectorPIMSExteriorGraph gamma gamma').Adj x y :=
      fun hext => hext.2.1 hvar.2
    simp [rlc_connectorPIMSAssembleConfig, SimpleGraph.mem_edgeSet,
      hvar, hnotext, hvar.1]
  · by_cases hext :
        (rlc_connectorPIMSExteriorGraph gamma gamma').Adj x y
    · simp [rlc_connectorPIMSAssembleConfig, SimpleGraph.mem_edgeSet,
        hvar, hext, hext.1]
    · simp [rlc_connectorPIMSAssembleConfig, SimpleGraph.mem_edgeSet,
        hvar, hext]


theorem rlc_connectorPIMSReflectedConfig_open_of_masked_open {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : Sym2 (RlcConnectorVertex n))
    (hnotTrace : rlc_pimsEdgeEquiv (e.map Subtype.val) ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1)
    (hopen : rlc_dualReflectConfig
      (rlc_maskConfig (rlc_connectorEdges gamma gamma')
        (rlc_connectorAmbientMixedConfig gamma gamma' tau))
      (e.map Subtype.val) = true) :
    rlc_connectorPIMSReflectedConfig gamma gamma' tau e = true := by
  rw [rlc_dualReflectConfig_eq_pims] at hopen
  rw [rlc_connectorPIMSReflectedConfig_apply]
  let source := rlc_pimsEdgeEquiv (e.map Subtype.val)
  by_cases hG : source ∈ rlc_connectorEdges gamma gamma'
  · simpa [source, rlc_maskConfig, hG] using hopen
  · have hsource :
        rlc_connectorAmbientMixedConfig gamma gamma' tau source = false := by
      simp [rlc_connectorAmbientMixedConfig, hG, hnotTrace, source]
    rw [hsource]
    rfl


end
end StatMech.Universality

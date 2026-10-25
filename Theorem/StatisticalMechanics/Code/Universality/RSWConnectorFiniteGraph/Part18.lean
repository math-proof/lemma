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
import Instance.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part8
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorPIMSExterior_reachable_iff_wiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (x y : RlcConnectorVertex n) :
    (rlc_connectorPIMSExteriorGraph gamma gamma').Reachable x y ↔
      (rlc_connectorPIMSExteriorWiring gamma gamma').Reachable x y := by
  constructor
  · apply Reachable.mono
    intro u v huv
    exact ⟨huv.ne, huv.reachable⟩
  · apply rlc_reachable_of_step_reachable
    intro u v huv
    exact huv.2


theorem rlc_connectorPIMSExterior_sup_reachable_iff_wiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H : SimpleGraph (RlcConnectorVertex n))
    (x y : RlcConnectorVertex n) :
    (H ⊔ rlc_connectorPIMSExteriorGraph gamma gamma').Reachable x y ↔
      (H ⊔ rlc_connectorPIMSExteriorWiring gamma gamma').Reachable x y := by
  constructor
  · apply Reachable.mono
    intro u v huv
    rcases huv with hH | hext
    · exact Or.inl hH
    · exact Or.inr ⟨hext.ne, hext.reachable⟩
  · apply rlc_reachable_of_step_reachable
    intro u v huv
    rcases huv with hH | hwire
    · exact (show (H ⊔
          rlc_connectorPIMSExteriorGraph gamma gamma').Adj u v
        from Or.inl hH).reachable
    · exact hwire.2.mono le_sup_right


theorem rlc_connectorFiniteGraph_eq_PIMS_preimage_partition {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    rlc_connectorFiniteGraph gamma gamma' =
      (rlc_connectorPIMSVariableGraph gamma gamma' ⊔
        rlc_connectorPIMSTraceGraph gamma gamma') ⊔
      rlc_connectorPIMSExteriorGraph gamma gamma' := by
  ext x y
  let source := rlc_pimsEdgeEquiv (s(x, y).map Subtype.val)
  constructor
  · intro hxy
    by_cases hsource : source ∈ rlc_connectorEdges gamma gamma'
    · exact Or.inl (Or.inl ⟨hxy, hsource⟩)
    · by_cases htrace :
          source ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1
      · exact Or.inl (Or.inr ⟨hxy, htrace⟩)
      · exact Or.inr ⟨hxy, hsource, htrace⟩
  · rintro ((⟨hxy, _⟩ | ⟨hxy, _⟩) | ⟨hxy, _, _⟩) <;> exact hxy


theorem rlc_openSub_PIMS_trace_eq_bot {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.openSub (rlc_connectorPIMSTraceGraph gamma gamma')
      (rlc_connectorPIMSReflectedConfig gamma gamma' tau) = ⊥ := by
  ext x y
  rw [FK.openSub_adj]
  constructor
  · rintro ⟨hxy, hopen⟩
    have hclosed := rlc_connectorPIMSReflectedConfig_of_preimage_trace
      gamma gamma' tau s(x, y) hxy.2
    exact (Bool.false_ne_true (hclosed.symm.trans hopen)).elim
  · intro hbot
    exact hbot.elim


theorem rlc_openSub_PIMS_eq_variable_sup_exterior {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.openSub (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorPIMSReflectedConfig gamma gamma' tau) =
      FK.openSub (rlc_connectorPIMSVariableGraph gamma gamma')
          (rlc_connectorPIMSReflectedConfig gamma gamma' tau) ⊔
        rlc_connectorPIMSExteriorGraph gamma gamma' := by
  ext x y
  rw [FK.openSub_adj, SimpleGraph.sup_adj, FK.openSub_adj]
  let source := rlc_pimsEdgeEquiv (s(x, y).map Subtype.val)
  constructor
  · rintro ⟨hxy, hopen⟩
    by_cases hsource : source ∈ rlc_connectorEdges gamma gamma'
    · exact Or.inl ⟨⟨hxy, hsource⟩, hopen⟩
    · by_cases htrace :
          source ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1
      · have hclosed := rlc_connectorPIMSReflectedConfig_of_preimage_trace
          gamma gamma' tau s(x, y) htrace
        exact (Bool.false_ne_true (hclosed.symm.trans hopen)).elim
      · exact Or.inr ⟨hxy, hsource, htrace⟩
  · rintro (⟨⟨hxy, hsource⟩, hopen⟩ | ⟨hxy, hsource, htrace⟩)
    · exact ⟨hxy, hopen⟩
    · refine ⟨hxy, ?_⟩
      exact rlc_connectorPIMSReflectedConfig_of_preimage_exterior
        gamma gamma' tau s(x, y) hsource htrace


theorem rlc_openSub_PIMSCollared_eq_variable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.openSub (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorPIMSCollaredReflectedConfig gamma gamma' tau) =
      FK.openSub (rlc_connectorPIMSVariableGraph gamma gamma')
        (rlc_connectorPIMSCollaredReflectedConfig gamma gamma' tau) := by
  ext x y
  rw [FK.openSub_adj, FK.openSub_adj]
  let source := rlc_pimsEdgeEquiv (s(x, y).map Subtype.val)
  constructor
  · rintro ⟨hxy, hopen⟩
    by_cases hsource : source ∈ rlc_connectorEdges gamma gamma'
    · exact ⟨⟨hxy, hsource⟩, hopen⟩
    · by_cases htrace :
          source ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1
      · have hclosed :=
          rlc_connectorPIMSCollaredReflectedConfig_of_preimage_trace
            gamma gamma' tau s(x, y) htrace
        exact (Bool.false_ne_true (hclosed.symm.trans hopen)).elim
      · have hclosed :=
          rlc_connectorPIMSCollaredReflectedConfig_of_preimage_exterior
            gamma gamma' tau s(x, y) hxy.2 hsource htrace
        exact (Bool.false_ne_true (hclosed.symm.trans hopen)).elim
  · rintro ⟨⟨hxy, _hsource⟩, hopen⟩
    exact ⟨hxy, hopen⟩


end
end StatMech.Universality

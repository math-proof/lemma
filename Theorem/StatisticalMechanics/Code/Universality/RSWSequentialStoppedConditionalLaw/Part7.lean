/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWSequentialStoppedExplorationBridge
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorSeededMassCapstone.Part2
import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEquiv.Part2
import Theorem.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part3
import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxDomainMarkov.Part3
import Def.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw.Part9
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_finiteExtremalPairCandidate_dependsOn {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    _root_.DependsOn
      ((rlc_finiteExtremalPairCandidate gamma gamma').indicator
        (fun _ => (1 : Real)))
      (rlc_finiteExtremalPairCandidateEdges gamma gamma' :
        Set (Sym2 (RlcConnectorVertex n))) := by
  intro psi rho hagree
  apply rlc_extremalPairCandidate_dependsOn
  intro e he
  obtain ⟨f, rfl⟩ :=
    rlc_extremalPairCandidateEdge_exists_connectorLift gamma gamma' he
  rw [rlc_connectorExtendConfig_apply, rlc_connectorExtendConfig_apply]
  exact hagree f (by
    have he' : f.map Subtype.val ∈
        rlc_extremalPairCandidateEdges (gamma, gamma') := he
    simp [rlc_finiteExtremalPairCandidateEdges, he'])


theorem rlc_connectorRestrictConfig_mem_finiteExtremalPairCandidate_iff
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    rlc_connectorRestrictConfig omega ∈
        rlc_finiteExtremalPairCandidate gamma gamma' ↔
      omega ∈ rlc_extremalPairCandidate (gamma, gamma') := by
  change rlc_connectorExtendConfig (rlc_connectorRestrictConfig omega) ∈
      rlc_extremalPairCandidate (gamma, gamma') ↔
    omega ∈ rlc_extremalPairCandidate (gamma, gamma')
  apply indic_iff
  apply rlc_extremalPairCandidate_dependsOn
  intro e he
  obtain ⟨f, rfl⟩ :=
    rlc_extremalPairCandidateEdge_exists_connectorLift gamma gamma' he
  rw [rlc_connectorExtendConfig_apply]
  rfl


theorem rlc_finiteExtremalPairCandidate_dependsOnOutside {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hdisj : Disjoint
      (rlc_finiteExtremalPairCandidateEdges gamma gamma')
      (rlc_connectorFiniteGraph gamma gamma').edgeFinset) :
    FK.DependsOnOutside
      (rlc_connectorFiniteGraph gamma gamma').edgeFinset
      (rlc_finiteExtremalPairCandidate gamma gamma') := by
  intro psi rho hagree
  apply indic_iff
  apply rlc_finiteExtremalPairCandidate_dependsOn
  intro e he
  exact (hagree e (fun heG =>
    (Finset.disjoint_left.mp hdisj) he heG)).symm


theorem rlc_finiteExtremalPairCandidateEdges_disjoint_connector_of_ambient
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hdisj : Disjoint (rlc_extremalPairCandidateEdges (gamma, gamma'))
      (rlc_connectorEdges gamma gamma')) :
    Disjoint (rlc_finiteExtremalPairCandidateEdges gamma gamma')
      (rlc_connectorFiniteGraph gamma gamma').edgeFinset := by
  rw [Finset.disjoint_left]
  intro e heCandidate heConnector
  have heCandidate' : e.map Subtype.val ∈
      rlc_extremalPairCandidateEdges (gamma, gamma') :=
    (Finset.mem_filter.mp heCandidate).2
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeFinset] at heConnector
      exact (Finset.disjoint_left.mp hdisj)
        (by simpa [Sym2.map_mk] using heCandidate') heConnector.2


theorem rlc_finiteExtremalPairCandidate_trace_open {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {psi : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (hpsi : psi ∈ rlc_finiteExtremalPairCandidate gamma gamma') :
    ∀ e ∈ (rlc_connectorTraceWiring gamma gamma').edgeFinset,
      psi e = true := by
  intro e he
  have hselected : rlc_connectorExtendConfig psi ∈
      rlc_extremalPairCandidate (gamma, gamma') := hpsi
  have hopen := rlc_extremalPairCandidate_subset_pathPairOpen
    (gamma, gamma') hselected
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeFinset] at he
      rcases Finset.mem_union.mp he.2 with hright | hleft
      · have := hopen.1 s((x : Site 2), (y : Site 2)) hright
        rw [← rlc_connectorExtendConfig_apply psi s(x, y)]
        simpa [Sym2.map_mk] using this
      · have := hopen.2 s((x : Site 2), (y : Site 2)) hleft
        rw [← rlc_connectorExtendConfig_apply psi s(x, y)]
        simpa [Sym2.map_mk] using this


end
end StatMech.Universality

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
import Structure.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_rightExploredVertices_subset_of_pathVertices_subset
    {n : Int} {gamma delta : RlcRightDiagonalPath n}
    (hverts : rlc_pathVertices delta.1 ⊆
      rlc_pathVertices gamma.1) :
    rlc_rightExploredVertices delta ⊆
      rlc_rightExploredVertices gamma := by
  have hdisj : Disjoint (rlc_strictTopSet gamma)
      (rlc_pathVertices delta.1 : Set (Site 2)) := by
    rw [Set.disjoint_left]
    intro z hzTop hzDelta
    exact (Set.disjoint_left.mp
      (rlc_strictTopSet_disjoint_path gamma)) hzTop (hverts hzDelta)
  have htop : rlc_strictTopSet gamma ⊆ rlc_strictTopSet delta :=
    rlc_strictTopSet_mono_of_disjoint_path gamma delta hdisj
  intro z hz
  rw [rlc_rightExploredVertices, Finset.mem_sdiff] at hz ⊢
  exact ⟨hz.1, fun hzTop => hz.2 (by
    rw [rlc_mem_strictTopVertices] at hzTop ⊢
    exact htop hzTop)⟩


theorem rlc_leftExploredVertices_subset_of_pathVertices_subset
    {n : Int} {gamma delta : RlcLeftDiagonalPath n}
    (hverts : rlc_pathVertices delta.1 ⊆
      rlc_pathVertices gamma.1) :
    rlc_leftExploredVertices delta ⊆
      rlc_leftExploredVertices gamma := by
  have hdisj : Disjoint (rlc_strictBottomSet gamma)
      (rlc_pathVertices delta.1 : Set (Site 2)) := by
    rw [Set.disjoint_left]
    intro z hzBottom hzDelta
    exact (Set.disjoint_left.mp
      (rlc_strictBottomSet_disjoint_path gamma)) hzBottom (hverts hzDelta)
  have hbottom : rlc_strictBottomSet gamma ⊆
      rlc_strictBottomSet delta :=
    rlc_strictBottomSet_mono_of_disjoint_path gamma delta hdisj
  intro z hz
  rw [rlc_leftExploredVertices, Finset.mem_sdiff] at hz ⊢
  exact ⟨hz.1, fun hzBottom => hz.2 (by
    rw [rlc_mem_strictBottomVertices] at hzBottom ⊢
    exact hbottom hzBottom)⟩


theorem rlc_rightLowestCandidate_explored_eq_of_open_subset
    {n : Int} {gamma delta : RlcRightDiagonalPath n}
    {omega : ConfigSpace (Sym2 (Site 2))}
    (hgamma : omega ∈ rlc_rightLowestCandidate gamma)
    (hdelta : omega ∈ rlc_pathOpen delta.1)
    (hsub : rlc_rightExploredVertices delta ⊆
      rlc_rightExploredVertices gamma) :
    rlc_rightExploredVertices delta =
      rlc_rightExploredVertices gamma := by
  by_contra hne
  have hstrict : rlc_rightExploredVertices delta ⊂
      rlc_rightExploredVertices gamma :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
  exact (rlc_rightLowestCandidate_not_open_of_below hgamma
    (Or.inl hstrict)) hdelta


theorem rlc_leftHighestCandidate_explored_eq_of_open_subset
    {n : Int} {gamma delta : RlcLeftDiagonalPath n}
    {omega : ConfigSpace (Sym2 (Site 2))}
    (hgamma : omega ∈ rlc_leftHighestCandidate gamma)
    (hdelta : omega ∈ rlc_pathOpen delta.1)
    (hsub : rlc_leftExploredVertices delta ⊆
      rlc_leftExploredVertices gamma) :
    rlc_leftExploredVertices delta =
      rlc_leftExploredVertices gamma := by
  by_contra hne
  have hstrict : rlc_leftExploredVertices delta ⊂
      rlc_leftExploredVertices gamma :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
  exact (rlc_leftHighestCandidate_not_open_of_above hgamma
    (Or.inl hstrict)) hdelta


theorem RlcBookFaithfulStratumReplacement.of_subpaths
    {n : Int}
    {gamma delta : RlcRightDiagonalPath n}
    {gamma' delta' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair delta delta')
    (hrEdges : rlc_pathEdges delta.1 ⊆ rlc_pathEdges gamma.1)
    (hlEdges : rlc_pathEdges delta'.1 ⊆ rlc_pathEdges gamma'.1)
    (hrVerts : rlc_pathVertices delta.1 ⊆ rlc_pathVertices gamma.1)
    (hlVerts : rlc_pathVertices delta'.1 ⊆ rlc_pathVertices gamma'.1)
    (hactive : (rlc_extremalPairCandidate (gamma, gamma')).Nonempty) :
    RlcBookFaithfulStratumReplacement gamma gamma' delta delta' := by
  obtain ⟨omega, hright, hleft⟩ := hactive
  have hopen := rlc_extremalPairCandidate_subset_pathPairOpen
    (gamma, gamma') ⟨hright, hleft⟩
  have hdelta : omega ∈ rlc_pathOpen delta.1 := fun e he =>
    hopen.1 e (hrEdges he)
  have hdelta' : omega ∈ rlc_pathOpen delta'.1 := fun e he =>
    hopen.2 e (hlEdges he)
  exact {
    faithful := hfaith
    right_edges := hrEdges
    left_edges := hlEdges
    right_explored := rlc_rightLowestCandidate_explored_eq_of_open_subset
      hright hdelta
        (rlc_rightExploredVertices_subset_of_pathVertices_subset hrVerts)
    left_explored := rlc_leftHighestCandidate_explored_eq_of_open_subset
      hleft hdelta'
        (rlc_leftExploredVertices_subset_of_pathVertices_subset hlVerts) }


theorem RlcBookFaithfulStratumReplacement.extremalPairCandidateEdges_disjoint_connectorEdges
    {n : Int}
    {gamma delta : RlcRightDiagonalPath n}
    {gamma' delta' : RlcLeftDiagonalPath n}
    (R : RlcBookFaithfulStratumReplacement gamma gamma' delta delta') :
    Disjoint (rlc_extremalPairCandidateEdges (gamma, gamma'))
      (rlc_connectorEdges delta delta') := by
  rw [Finset.disjoint_left]
  intro e heCandidate heConnector
  have hexplored := rlc_extremalPairCandidateEdges_subset_explored
    gamma gamma' heCandidate
  have hconnector := (Finset.mem_filter.mp heConnector).2
  obtain ⟨z, hzRegion, hzEdge⟩ := hconnector
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [Finset.mem_union] at hexplored
      rw [Sym2.mem_iff] at hzEdge
      rcases hexplored with hright | hleft
      · rw [mem_edgesWithinFinset] at hright
        obtain ⟨u, hu, v, hv, huv⟩ := hright
        have hends : x ∈ rlc_rightExploredVertices gamma ∧
            y ∈ rlc_rightExploredVertices gamma := by
          rw [Sym2.eq_iff] at huv
          rcases huv with ⟨hxu, hyv⟩ | ⟨hxv, hyu⟩
          · subst u
            subst v
            exact ⟨hu, hv⟩
          · subst v
            subst u
            exact ⟨hv, hu⟩
        obtain ⟨hx, hy⟩ := hends
        rw [← R.right_explored, rlc_rightExploredVertices,
          Finset.mem_sdiff, rlc_mem_rectFinset, mem_rect] at hx hy
        rcases hzEdge with hzEdge | hzEdge
        · subst z
          exact hx.2 (by
            rw [rlc_mem_strictTopVertices]
            exact R.faithful.connectorOriginRegion_mem_strictTopSet
              (z := x) hzRegion hx.1.1)
        · subst z
          exact hy.2 (by
            rw [rlc_mem_strictTopVertices]
            exact R.faithful.connectorOriginRegion_mem_strictTopSet
              (z := y) hzRegion hy.1.1)
      · rw [mem_edgesWithinFinset] at hleft
        obtain ⟨u, hu, v, hv, huv⟩ := hleft
        have hends : x ∈ rlc_leftExploredVertices gamma' ∧
            y ∈ rlc_leftExploredVertices gamma' := by
          rw [Sym2.eq_iff] at huv
          rcases huv with ⟨hxu, hyv⟩ | ⟨hxv, hyu⟩
          · subst u
            subst v
            exact ⟨hu, hv⟩
          · subst v
            subst u
            exact ⟨hv, hu⟩
        obtain ⟨hx, hy⟩ := hends
        rw [← R.left_explored, rlc_leftExploredVertices,
          Finset.mem_sdiff, rlc_mem_rectFinset, mem_rect] at hx hy
        rcases hzEdge with hzEdge | hzEdge
        · subst z
          exact hx.2 (by
            rw [rlc_mem_strictBottomVertices]
            exact R.faithful.connectorOriginRegion_mem_strictBottomSet
              (z := x) hzRegion hx.1.2.1)
        · subst z
          exact hy.2 (by
            rw [rlc_mem_strictBottomVertices]
            exact R.faithful.connectorOriginRegion_mem_strictBottomSet
              (z := y) hzRegion hy.1.2.1)


theorem RlcBookFaithfulTracePair.finiteExtremalPairCandidateEdges_disjoint_connector
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    Disjoint (rlc_finiteExtremalPairCandidateEdges gamma gamma')
      (rlc_connectorFiniteGraph gamma gamma').edgeFinset :=
  rlc_finiteExtremalPairCandidateEdges_disjoint_connector_of_ambient
    gamma gamma'
      hfaith.extremalPairCandidateEdges_disjoint_connectorEdges


theorem RlcBookFaithfulStratumReplacement.finiteExtremalPairCandidateEdges_disjoint_connector
    {n : Int}
    {gamma delta : RlcRightDiagonalPath n}
    {gamma' delta' : RlcLeftDiagonalPath n}
    (R : RlcBookFaithfulStratumReplacement gamma gamma' delta delta') :
    Disjoint (rlc_finiteExtremalPairCandidateEdges gamma gamma')
      (rlc_connectorFiniteGraph delta delta').edgeFinset := by
  rw [Finset.disjoint_left]
  intro e heCandidate heConnector
  have heCandidate' : e.map Subtype.val ∈
      rlc_extremalPairCandidateEdges (gamma, gamma') :=
    (Finset.mem_filter.mp heCandidate).2
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeFinset] at heConnector
      exact (Finset.disjoint_left.mp
        R.extremalPairCandidateEdges_disjoint_connectorEdges)
          (by simpa [Sym2.map_mk] using heCandidate') heConnector.2


theorem RlcBookFaithfulStratumReplacement.finiteExtremalPairCandidate_trace_open
    {n : Int}
    {gamma delta : RlcRightDiagonalPath n}
    {gamma' delta' : RlcLeftDiagonalPath n}
    (R : RlcBookFaithfulStratumReplacement gamma gamma' delta delta')
    {psi : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (hpsi : psi ∈ rlc_finiteExtremalPairCandidate gamma gamma') :
    ∀ e ∈ (rlc_connectorTraceWiring delta delta').edgeFinset,
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
      · have hopenEdge := hopen.1 s((x : Site 2), (y : Site 2))
          (R.right_edges hright)
        rw [← rlc_connectorExtendConfig_apply psi s(x, y)]
        simpa [Sym2.map_mk] using hopenEdge
      · have hopenEdge := hopen.2 s((x : Site 2), (y : Site 2))
          (R.left_edges hleft)
        rw [← rlc_connectorExtendConfig_apply psi s(x, y)]
        simpa [Sym2.map_mk] using hopenEdge


theorem RlcBookFaithfulStratumReplacement.compatibleExteriorFibre
    {n : Int}
    {gamma delta : RlcRightDiagonalPath n}
    {gamma' delta' : RlcLeftDiagonalPath n}
    (R : RlcBookFaithfulStratumReplacement gamma gamma' delta delta')
    (H : SimpleGraph (RlcConnectorVertex n))
    (hGH : rlc_connectorFiniteGraph delta delta' ≤ H)
    (hTH : rlc_connectorTraceWiring delta delta' ≤ H)
    {psi : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (hpsi : psi ∈ rlc_finiteExtremalPairCandidate gamma gamma') :
    RlcConnectorCompatibleExteriorFibre delta delta' H psi where
  connector_le := hGH
  trace_le := hTH
  trace_open := R.finiteExtremalPairCandidate_trace_open hpsi


theorem rlc_finiteExtremalPairCandidate_compatibleExteriorFibre {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H : SimpleGraph (RlcConnectorVertex n))
    (hGH : rlc_connectorFiniteGraph gamma gamma' ≤ H)
    (hTH : rlc_connectorTraceWiring gamma gamma' ≤ H)
    {psi : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (hpsi : psi ∈ rlc_finiteExtremalPairCandidate gamma gamma') :
    RlcConnectorCompatibleExteriorFibre gamma gamma' H psi where
  connector_le := hGH
  trace_le := hTH
  trace_open := rlc_finiteExtremalPairCandidate_trace_open
    gamma gamma' hpsi


theorem RlcSequentialExtremalExplorationState.toCompatibleExteriorFibre
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (S : RlcSequentialExtremalExplorationState gamma gamma')
    (H : SimpleGraph (RlcConnectorVertex n))
    (hGH : rlc_connectorFiniteGraph gamma gamma' ≤ H)
    (hTH : rlc_connectorTraceWiring gamma gamma' ≤ H) :
    RlcConnectorCompatibleExteriorFibre gamma gamma' H
      (rlc_connectorRestrictConfig S.rawConfig) where
  connector_le := hGH
  trace_le := hTH
  trace_open := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ x y =>
        rw [SimpleGraph.mem_edgeFinset] at he
        change S.rawConfig s((x : Site 2), (y : Site 2)) = true
        rcases Finset.mem_union.mp he.2 with hright | hleft
        · exact S.rightTrace_open hright
        · exact S.leftTrace_open hleft


theorem RlcConnectorCompatibleExteriorFibre.trace_le_frozenExterior
    {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {H : SimpleGraph (RlcConnectorVertex n)}
    {psi : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (F : RlcConnectorCompatibleExteriorFibre gamma gamma' H psi)
    (B : SimpleGraph (RlcConnectorVertex n)) :
    rlc_connectorTraceWiring gamma gamma' ≤
      rlc_connectorFrozenExteriorGraph gamma gamma' H B psi := by
  intro x y hxy
  left
  refine ⟨F.trace_le hxy, ?_, F.trace_open s(x, y) ?_⟩
  · intro hG
    exact rlc_connectorFiniteGraph_adj_not_traceWiring
      gamma gamma' hG hxy
  · rw [SimpleGraph.mem_edgeFinset]
    exact hxy


theorem RlcConnectorCompatibleExteriorFibre.separate_le_inducedWiring
    {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {H : SimpleGraph (RlcConnectorVertex n)}
    {psi : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (F : RlcConnectorCompatibleExteriorFibre gamma gamma' H psi)
    (B : SimpleGraph (RlcConnectorVertex n)) :
    rlc_connectorSeparateWiring gamma gamma' ≤
      rlc_connectorExteriorInducedWiring gamma gamma' H B psi := by
  intro x y hxy
  rw [rlc_connectorSeparateWiring, SimpleGraph.sup_adj] at hxy
  refine ⟨?_, ?_⟩
  · rcases hxy with hright | hleft
    · rw [Lattice.boundaryCliqueGraph_adj] at hright
      exact hright.1
    · rw [Lattice.boundaryCliqueGraph_adj] at hleft
      exact hleft.1
  · rcases hxy with hright | hleft
    · rw [Lattice.boundaryCliqueGraph_adj] at hright
      exact (rlc_connectorTraceWiring_reachable_right gamma gamma'
        hright.2.1 hright.2.2).mono (F.trace_le_frozenExterior B)
    · rw [Lattice.boundaryCliqueGraph_adj] at hleft
      exact (rlc_connectorTraceWiring_reachable_left gamma gamma'
        hleft.2.1 hleft.2.2).mono (F.trace_le_frozenExterior B)


end
end StatMech.Universality

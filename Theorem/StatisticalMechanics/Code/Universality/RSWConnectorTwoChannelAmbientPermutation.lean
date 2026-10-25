/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelAmbientPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelStaticCutEndpoint
import Theorem.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw.Part16
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelAmbientPermutation
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysicalAmbientFailureEmbedding_success
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection
      gamma gamma' hfaith)
    (rho : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
      rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'}) :
    rlc_twoChannelFullPhysicalAmbientFailureEmbedding hfaith hstatic rho ∈
      rlc_finiteTwoChannelConnectorEvent gamma gamma' := by
  exact rlc_twoChannelLiftEdgeFailureEmbedding_success gamma gamma'
    (rlc_twoChannelFullPhysicalSuccessEmbedding hfaith
      (rlc_twoChannelFullPhysicalPermutationSuccess_of_staticCutIntersection
        hfaith hstatic)) rho


theorem rlc_twoChannelFullPhysicalAmbientFailureEmbedding_apply_of_not_edge
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection
      gamma gamma' hfaith)
    (rho : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
      rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'})
    (e : Sym2 (RlcConnectorVertex n))
    (he : e ∉ (rlc_connectorTwoChannelGraph gamma gamma').edgeSet) :
    rlc_twoChannelFullPhysicalAmbientFailureEmbedding hfaith hstatic rho e =
      rho.1 e := by
  change rlc_twoChannelEdgeConfigCombine gamma gamma' _
      ((rlc_twoChannelConfigSplitEquiv gamma gamma' rho.1).2) e = rho.1 e
  simp [rlc_twoChannelEdgeConfigCombine, rlc_twoChannelConfigSplitEquiv, he]


theorem rlc_twoChannelFullPhysicalAmbientFailureEmbedding_agreesOff
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection
      gamma gamma' hfaith)
    (rho : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
      rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'}) :
    FK.AgreesOff (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset rho.1
      (rlc_twoChannelFullPhysicalAmbientFailureEmbedding
        hfaith hstatic rho) := by
  intro e he
  apply rlc_twoChannelFullPhysicalAmbientFailureEmbedding_apply_of_not_edge
  simpa [SimpleGraph.mem_edgeFinset] using he


theorem rlc_connectorTwoChannelGraph_edgeFinset_disjoint_traceWiring
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) :
    Disjoint (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset
      (rlc_connectorTraceWiring gamma gamma').edgeFinset := by
  rw [Finset.disjoint_left]
  intro e heChannel heTrace
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeFinset] at heChannel heTrace
      exact heChannel.2 heTrace


theorem rlc_connectorExtendConfig_pathPairOpen_of_trace_open
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (htrace : ∀ e ∈ (rlc_connectorTraceWiring gamma gamma').edgeFinset,
      psi e = true) :
    rlc_connectorExtendConfig psi ∈ rlc_pathPairOpen (gamma, gamma') := by
  constructor
  · intro e he
    have heCandidate :
        e ∈ rlc_extremalPairCandidateEdges (gamma, gamma') := by
      rw [rlc_extremalPairCandidateEdges, rlc_rightLowestCandidateEdges,
        Finset.mem_union, Finset.mem_union]
      exact Or.inl (Or.inl he)
    obtain ⟨f, rfl⟩ :=
      rlc_extremalPairCandidateEdge_exists_connectorLift
        gamma gamma' heCandidate
    rw [rlc_connectorExtendConfig_apply]
    apply htrace
    induction f using Sym2.inductionOn with
    | _ x y =>
        rw [SimpleGraph.mem_edgeFinset]
        exact ⟨rlc_pathEdge_lattice gamma.1 (by simpa using he),
          Finset.mem_union_left _ (by simpa using he)⟩
  · intro e he
    have heCandidate :
        e ∈ rlc_extremalPairCandidateEdges (gamma, gamma') := by
      rw [rlc_extremalPairCandidateEdges, rlc_leftHighestCandidateEdges,
        Finset.mem_union, Finset.mem_union]
      exact Or.inr (Or.inl he)
    obtain ⟨f, rfl⟩ :=
      rlc_extremalPairCandidateEdge_exists_connectorLift
        gamma gamma' heCandidate
    rw [rlc_connectorExtendConfig_apply]
    apply htrace
    induction f using Sym2.inductionOn with
    | _ x y =>
        rw [SimpleGraph.mem_edgeFinset]
        exact ⟨rlc_pathEdge_lattice gamma'.1 (by simpa using he),
          Finset.mem_union_right _ (by simpa using he)⟩


theorem rlc_allOpenConnectorConfig_displays_two_pathPairs
    {n : Int} (pair pair' : RlcDiagonalPathPair n) :
    let psi : ConfigSpace (Sym2 (RlcConnectorVertex n)) := fun _ ↦ true
    rlc_connectorExtendConfig psi ∈ rlc_pathPairOpen pair ∩
      rlc_pathPairOpen pair' := by
  dsimp only
  constructor
  · apply rlc_connectorExtendConfig_pathPairOpen_of_trace_open
    simp
  · apply rlc_connectorExtendConfig_pathPairOpen_of_trace_open
    simp


end
end StatMech.Universality

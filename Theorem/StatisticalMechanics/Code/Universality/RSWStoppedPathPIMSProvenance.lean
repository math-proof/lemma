/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedPathPIMSProvenance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWAxisGapPIMSAnchoredSide.Part3
import Def.StatisticalMechanics.Code.Universality.RSWStoppedPathPIMSProvenance.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_extremalPairCandidateEdges_subset_explored {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    rlc_extremalPairCandidateEdges (gamma, gamma') ⊆
      StatMech.Percolation.edgesWithinFinset
          (rlc_rightExploredVertices gamma) ∪
        StatMech.Percolation.edgesWithinFinset
          (rlc_leftExploredVertices gamma') := by
  intro e he
  change e ∈ rlc_rightLowestCandidateEdges gamma ∪
    rlc_leftHighestCandidateEdges gamma' at he
  rw [Finset.mem_union] at he ⊢
  rcases he with he | he
  · exact Or.inl (rlc_rightLowestCandidateEdges_subset gamma he)
  · exact Or.inr (rlc_leftHighestCandidateEdges_subset gamma' he)


@[simp] theorem rlc_sequentialExtremalClosedComparison_of_mem
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n} (omega : ConfigSpace (Sym2 (Site 2)))
    {e : Sym2 (Site 2)}
    (he : e ∈ rlc_sequentialExtremalExteriorEdges gamma gamma') :
    rlc_sequentialExtremalClosedComparison gamma gamma' omega e = false := by
  simp [rlc_sequentialExtremalClosedComparison, he]


theorem rlc_sequentialExtremalClosedComparison_of_not_mem
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n} (omega : ConfigSpace (Sym2 (Site 2)))
    {e : Sym2 (Site 2)}
    (he : e ∉ rlc_sequentialExtremalExteriorEdges gamma gamma') :
    rlc_sequentialExtremalClosedComparison gamma gamma' omega e = omega e := by
  simp [rlc_sequentialExtremalClosedComparison, he]


theorem RlcSequentialExtremalExplorationState.pathPairOpen
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (S : RlcSequentialExtremalExplorationState gamma gamma') :
    S.rawConfig ∈ rlc_pathPairOpen (gamma, gamma') :=
  rlc_extremalPairCandidate_subset_pathPairOpen (gamma, gamma') S.selected


theorem RlcSequentialExtremalExplorationState.rightTrace_open
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (S : RlcSequentialExtremalExplorationState gamma gamma')
    {e : Sym2 (Site 2)} (he : e ∈ rlc_pathEdges gamma.1) :
    S.rawConfig e = true :=
  S.pathPairOpen.1 e he


theorem RlcSequentialExtremalExplorationState.leftTrace_open
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (S : RlcSequentialExtremalExplorationState gamma gamma')
    {e : Sym2 (Site 2)} (he : e ∈ rlc_pathEdges gamma'.1) :
    S.rawConfig e = true :=
  S.pathPairOpen.2 e he


end
end StatMech.Universality

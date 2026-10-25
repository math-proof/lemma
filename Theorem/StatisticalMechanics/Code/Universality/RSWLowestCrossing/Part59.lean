/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Theorem.StatisticalMechanics.Code.Percolation.OffClusterIndep.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Inequalities.Harris
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
import Theorem.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part13
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part58
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_leftHighestCandidateEdges_subset {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) :
    rlc_leftHighestCandidateEdges gamma ⊆
      edgesWithinFinset (rlc_leftExploredVertices gamma) := by
  classical
  intro e he
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [mem_edgesWithinFinset]
      have hxy : x ∈ rlc_leftExploredVertices gamma ∧
          y ∈ rlc_leftExploredVertices gamma := by
        rw [rlc_leftHighestCandidateEdges, Finset.mem_union] at he
        rcases he with hePath | heUpper
        · have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 hePath
          exact ⟨rlc_leftPathVertex_mem_explored gamma hends.1,
            rlc_leftPathVertex_mem_explored gamma hends.2⟩
        · simp only [rlc_leftUpperPathEdges, Finset.mem_biUnion,
              Finset.mem_filter, Finset.mem_univ, true_and] at heUpper
          obtain ⟨delta, habove, heDelta⟩ := heUpper
          have hends := rlc_pathEdge_endpoints_mem_vertices delta.1 heDelta
          have hsub : rlc_leftExploredVertices delta ⊆
              rlc_leftExploredVertices gamma := by
            rcases habove with hstrict | heq
            · exact (Finset.ssubset_iff_subset_ne.mp hstrict).1
            · simpa [heq.1]
          constructor
          · exact hsub (rlc_leftPathVertex_mem_explored delta hends.1)
          · exact hsub (rlc_leftPathVertex_mem_explored delta hends.2)
      show ∃ x' ∈ rlc_leftExploredVertices gamma,
        ∃ y' ∈ rlc_leftExploredVertices gamma, s(x, y) = s(x', y')
      exact ⟨x, hxy.1, y, hxy.2, rfl⟩

theorem rlc_leftHighestCandidate_dependsOn {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) :
    DependsOn ((rlc_leftHighestCandidate gamma).indicator (fun _ => (1 : ℝ)))
      (rlc_leftHighestCandidateEdges gamma : Set (Sym2 (Site 2))) := by
  classical
  intro omega omega' hagree
  have hgamma : omega ∈ rlc_pathOpen gamma.1 ↔
      omega' ∈ rlc_pathOpen gamma.1 := by
    apply indic_iff
    apply rlc_pathOpen_dependsOn gamma.1
    intro e he
    exact hagree e (by
      simp only [rlc_leftHighestCandidateEdges, Finset.mem_coe,
        Finset.mem_union]
      exact Or.inl he)
  have hdelta : ∀ (delta : RlcLeftDiagonalPath n),
      rlc_leftPathAbove delta gamma →
      (omega ∈ rlc_pathOpen delta.1 ↔ omega' ∈ rlc_pathOpen delta.1) := by
    intro delta habove
    apply indic_iff
    apply rlc_pathOpen_dependsOn delta.1
    intro e he
    exact hagree e (by
      simp only [rlc_leftHighestCandidateEdges, Finset.mem_coe,
        Finset.mem_union]
      exact Or.inr (rlc_mem_leftUpperPathEdges habove he))
  have hupper :
      (omega ∈ ⋃ delta : RlcLeftDiagonalPath n,
          if rlc_leftPathAbove delta gamma then
            rlc_pathOpen delta.1 else ∅) ↔
      (omega' ∈ ⋃ delta : RlcLeftDiagonalPath n,
          if rlc_leftPathAbove delta gamma then
            rlc_pathOpen delta.1 else ∅) := by
    simp only [Set.mem_iUnion]
    apply exists_congr
    intro delta
    by_cases habove : rlc_leftPathAbove delta gamma
    · simpa [habove] using hdelta delta habove
    · simp [habove]
  have hevent : omega ∈ rlc_leftHighestCandidate gamma ↔
      omega' ∈ rlc_leftHighestCandidate gamma := by
    change (_ ∧ ¬ _) ↔ (_ ∧ ¬ _)
    rw [hgamma, hupper]
  by_cases hmem : omega ∈ rlc_leftHighestCandidate gamma
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hevent.mp hmem)]
  · rw [Set.indicator_of_notMem hmem,
      Set.indicator_of_notMem (fun h => hmem (hevent.mpr h))]


theorem rlc_iUnion_leftHighestCandidate (n : ℤ) :
    (⋃ gamma : RlcLeftDiagonalPath n, rlc_leftHighestCandidate gamma) =
      rlc_leftDiagonal n := by
  calc
    _ = ⋃ gamma : RlcLeftDiagonalPath n, rlc_pathOpen gamma.1 := by
      simpa only [rlc_leftHighestCandidate, rlc_rankedMinimalCandidate] using
        (rlc_iUnion_rankedMinimalCandidate
          (W := fun gamma : RlcLeftDiagonalPath n => rlc_pathOpen gamma.1)
          rlc_leftPathAbove rlc_leftPathRank
          (fun h => rlc_leftPathAbove_rank_lt h))
    _ = rlc_leftDiagonal n := rlc_iUnion_leftDiagonalPath n


end Universality
end StatMech

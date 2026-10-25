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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part56
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_rightLowestCandidateEdges_subset {n : ℤ}
    (gamma : RlcRightDiagonalPath n) :
    rlc_rightLowestCandidateEdges gamma ⊆
      edgesWithinFinset (rlc_rightExploredVertices gamma) := by
  classical
  intro e he
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [mem_edgesWithinFinset]
      have hxy : x ∈ rlc_rightExploredVertices gamma ∧
          y ∈ rlc_rightExploredVertices gamma := by
        rw [rlc_rightLowestCandidateEdges, Finset.mem_union] at he
        rcases he with hePath | heLower
        · have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 hePath
          exact ⟨rlc_rightPathVertex_mem_explored gamma hends.1,
            rlc_rightPathVertex_mem_explored gamma hends.2⟩
        · simp only [rlc_rightLowerPathEdges, Finset.mem_biUnion,
              Finset.mem_filter, Finset.mem_univ, true_and] at heLower
          obtain ⟨delta, hbelow, heDelta⟩ := heLower
          have hends := rlc_pathEdge_endpoints_mem_vertices delta.1 heDelta
          have hsub : rlc_rightExploredVertices delta ⊆
              rlc_rightExploredVertices gamma := by
            rcases hbelow with hstrict | heq
            · exact (Finset.ssubset_iff_subset_ne.mp hstrict).1
            · simpa [heq.1]
          constructor
          · exact hsub (rlc_rightPathVertex_mem_explored delta hends.1)
          · exact hsub (rlc_rightPathVertex_mem_explored delta hends.2)
      exact ⟨x, hxy.1, y, hxy.2, rfl⟩

theorem rlc_rightLowestCandidate_dependsOn {n : ℤ}
    (gamma : RlcRightDiagonalPath n) :
    DependsOn ((rlc_rightLowestCandidate gamma).indicator (fun _ => (1 : ℝ)))
      (rlc_rightLowestCandidateEdges gamma : Set (Sym2 (Site 2))) := by
  classical
  intro omega omega' hagree
  have hgamma : omega ∈ rlc_pathOpen gamma.1 ↔
      omega' ∈ rlc_pathOpen gamma.1 := by
    apply indic_iff
    apply rlc_pathOpen_dependsOn gamma.1
    intro e he
    exact hagree e (by
      simp only [rlc_rightLowestCandidateEdges, Finset.mem_coe,
        Finset.mem_union]
      exact Or.inl he)
  have hdelta : ∀ (delta : RlcRightDiagonalPath n),
      rlc_rightPathBelow delta gamma →
      (omega ∈ rlc_pathOpen delta.1 ↔ omega' ∈ rlc_pathOpen delta.1) := by
    intro delta hbelow
    apply indic_iff
    apply rlc_pathOpen_dependsOn delta.1
    intro e he
    exact hagree e (by
      simp only [rlc_rightLowestCandidateEdges, Finset.mem_coe,
        Finset.mem_union]
      exact Or.inr (rlc_mem_rightLowerPathEdges hbelow he))
  have hlower :
      (omega ∈ ⋃ delta : RlcRightDiagonalPath n,
          if rlc_rightPathBelow delta gamma then
            rlc_pathOpen delta.1 else ∅) ↔
      (omega' ∈ ⋃ delta : RlcRightDiagonalPath n,
          if rlc_rightPathBelow delta gamma then
            rlc_pathOpen delta.1 else ∅) := by
    simp only [Set.mem_iUnion]
    apply exists_congr
    intro delta
    by_cases hbelow : rlc_rightPathBelow delta gamma
    · simpa [hbelow] using hdelta delta hbelow
    · simp [hbelow]
  have hevent : omega ∈ rlc_rightLowestCandidate gamma ↔
      omega' ∈ rlc_rightLowestCandidate gamma := by
    change (_ ∧ ¬ _) ↔ (_ ∧ ¬ _)
    rw [hgamma, hlower]
  by_cases hmem : omega ∈ rlc_rightLowestCandidate gamma
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hevent.mp hmem)]
  · rw [Set.indicator_of_notMem hmem,
      Set.indicator_of_notMem (fun h => hmem (hevent.mpr h))]


theorem rlc_iUnion_rightLowestCandidate (n : ℤ) :
    (⋃ gamma : RlcRightDiagonalPath n, rlc_rightLowestCandidate gamma) =
      rlc_rightDiagonal n := by
  calc
    _ = ⋃ gamma : RlcRightDiagonalPath n, rlc_pathOpen gamma.1 := by
      simpa only [rlc_rightLowestCandidate, rlc_rankedMinimalCandidate] using
        (rlc_iUnion_rankedMinimalCandidate
          (W := fun gamma : RlcRightDiagonalPath n => rlc_pathOpen gamma.1)
          rlc_rightPathBelow rlc_rightPathRank
          (fun h => rlc_rightPathBelow_rank_lt h))
    _ = rlc_rightDiagonal n := rlc_iUnion_rightDiagonalPath n


end Universality
end StatMech

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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part97
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_wiredConnectorConfig_congr {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (U : Finset (Sym2 (Site 2)))
    {omega omega' : ConfigSpace (Sym2 (Site 2))}
    (hagree : ∀ e ∈ (U : Set (Sym2 (Site 2))), omega e = omega' e) :
    rlc_wiredConnectorConfig gamma gamma' U omega =
      rlc_wiredConnectorConfig gamma gamma' U omega' := by
  have hmask : rlc_maskConfig U omega = rlc_maskConfig U omega' :=
    rlc_maskConfig_congr hagree
  funext e
  simp only [rlc_wiredConnectorConfig, hmask]

theorem rlc_wiredConnectorConfig_mono {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (U : Finset (Sym2 (Site 2)))
    {omega omega' : ConfigSpace (Sym2 (Site 2))} (h : omega ≤ omega') :
    rlc_wiredConnectorConfig gamma gamma' U omega ≤
      rlc_wiredConnectorConfig gamma gamma' U omega' := by
  intro e
  by_cases hp : e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1
  · simp [rlc_wiredConnectorConfig, hp]
  · simp only [rlc_wiredConnectorConfig, if_neg hp]
    exact rlc_maskConfig_mono U h e


theorem rlc_dualReflect_wired_open_of_support {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) {e : Sym2 (Site 2)}
    (heTarget : e ∈
      (rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) ∪
        rlc_mixedAxisGapEdges G)
    (heSource : rlc_pimsEdgeEquiv e ∈ rlc_mixedAxisGapEdges G)
    (hopen : rlc_dualReflectConfig
      (rlc_wiredConnectorConfig gamma gamma'
        (rlc_mixedAxisGapEdges G) omega) e = true) :
    rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G)
      (rlc_dualReflectConfig omega) e = true := by
  have hsourceNotPaths : rlc_pimsEdgeEquiv e ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
    intro he
    rw [Finset.mem_union] at he
    rcases he with he | he
    · exact (Finset.disjoint_left.mp
        (rlc_rightPathEdges_disjoint_mixedAxisGapEdges G)) he heSource
    · exact (Finset.disjoint_left.mp
        (rlc_leftPathEdges_disjoint_mixedAxisGapEdges G)) he heSource
  have hrawOpen : rlc_dualReflectConfig omega e = true := by
    rw [rlc_dualReflectConfig_eq_pims] at hopen ⊢
    rw [rlc_wiredConnectorConfig, if_neg hsourceNotPaths,
      rlc_maskConfig, if_pos heSource] at hopen
    exact hopen
  rw [Finset.mem_union] at heTarget
  rcases heTarget with hePath | heU
  · simp [rlc_wiredConnectorConfig, hePath]
  · by_cases hePath : e ∈
        rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1
    · simp [rlc_wiredConnectorConfig, hePath]
    · simp [rlc_wiredConnectorConfig, hePath, rlc_maskConfig, heU,
        hrawOpen]


theorem rlc_dualReflect_wired_walk_of_support {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) {x y : Site 2}
    (p : (openSubgraph 2 (rlc_dualReflectConfig
      (rlc_wiredConnectorConfig gamma gamma'
        (rlc_mixedAxisGapEdges G) omega))).Walk x y)
    (hsupport : ∀ e ∈ p.edges,
      e ∈ (rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) ∪
          rlc_mixedAxisGapEdges G ∧
        rlc_pimsEdgeEquiv e ∈ rlc_mixedAxisGapEdges G) :
    ∃ q : (openSubgraph 2
      (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G)
        (rlc_dualReflectConfig omega))).Walk x y,
      q.edges = p.edges ∧ q.support = p.support := by
  let H := openSubgraph 2
    (rlc_wiredConnectorConfig gamma gamma' (rlc_mixedAxisGapEdges G)
      (rlc_dualReflectConfig omega))
  have htransfer : ∀ e ∈ p.edges, e ∈ H.edgeSet := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
        have hadj := p.adj_of_mem_edges he
        rw [openSubgraph_adj] at hadj
        rw [SimpleGraph.mem_edgeSet, openSubgraph_adj]
        exact ⟨hadj.1, rlc_dualReflect_wired_open_of_support
          G omega (hsupport s(u, v) he).1 (hsupport s(u, v) he).2
            hadj.2⟩
  let q := p.transfer H htransfer
  exact ⟨q, p.edges_transfer htransfer, p.support_transfer htransfer⟩


theorem rlc_wiredConnectorConfig_le_of_pathOpen {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (U : Finset (Sym2 (Site 2)))
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hgamma : omega ∈ rlc_pathOpen gamma.1)
    (hgamma' : omega ∈ rlc_pathOpen gamma'.1) :
    rlc_wiredConnectorConfig gamma gamma' U omega ≤ omega := by
  intro e
  by_cases hp : e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1
  · have hopen : omega e = true := by
      rw [Finset.mem_union] at hp
      rcases hp with hp | hp
      · exact hgamma e hp
      · exact hgamma' e hp
    rw [rlc_wiredConnectorConfig, if_pos hp, hopen]
  · rw [rlc_wiredConnectorConfig, if_neg hp]
    exact rlc_maskConfig_le U omega e


end Universality
end StatMech

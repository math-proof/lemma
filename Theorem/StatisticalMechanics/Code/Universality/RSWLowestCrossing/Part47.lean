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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part46
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_jointBottomSet_subset_box {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) :
    rlc_jointBottomSet gamma delta ⊆ rect 0 (2 * n) (-n) n := by
  rintro z ⟨x, hxBottom, hxGamma, hxDelta, hreach⟩
  obtain ⟨w⟩ := hreach
  exact (rlc_rightPairAvoidGraph_walk_dest gamma delta
    hxBottom.1 hxGamma hxDelta w).1


theorem rlc_jointBottomSet_finite {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) :
    (rlc_jointBottomSet gamma delta).Finite :=
  (rect_finite 0 (2 * n) (-n) n).subset
    (rlc_jointBottomSet_subset_box gamma delta)

theorem rlc_jointBottomSet_disjoint_paths {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) :
    Disjoint (rlc_jointBottomSet gamma delta)
      ((rlc_pathVertices gamma.1 : Set (Site 2)) ∪
        rlc_pathVertices delta.1) := by
  rw [Set.disjoint_left]
  rintro z ⟨x, hxBottom, hxGamma, hxDelta, hreach⟩ hzPath
  obtain ⟨w⟩ := hreach
  have hz := rlc_rightPairAvoidGraph_walk_dest gamma delta
    hxBottom.1 hxGamma hxDelta w
  exact hzPath.elim hz.2.1 hz.2.2


theorem rlc_jointBottomSet_subset_commonStrictBelowSet {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) :
    rlc_jointBottomSet gamma delta ⊆
      rlc_commonStrictBelowSet gamma delta := by
  rintro z ⟨x, hxBottom, hxGamma, hxDelta, hreach⟩
  obtain ⟨w⟩ := hreach
  have wg : (rlc_rightPathAvoidGraph gamma).Walk x z := by
    apply w.transfer (rlc_rightPathAvoidGraph gamma)
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
        have huv := w.adj_of_mem_edges he
        exact ⟨huv.1, huv.2.1, huv.2.2.1,
          huv.2.2.2.1, huv.2.2.2.2.1⟩
  have wd : (rlc_rightPathAvoidGraph delta).Walk x z := by
    apply w.transfer (rlc_rightPathAvoidGraph delta)
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
        have huv := w.adj_of_mem_edges he
        exact ⟨huv.1, huv.2.1, huv.2.2.1,
          huv.2.2.2.2.2.1, huv.2.2.2.2.2.2⟩
  exact ⟨⟨x, hxBottom, hxGamma, ⟨wg⟩⟩,
    ⟨x, hxBottom, hxDelta, ⟨wd⟩⟩⟩


theorem rlc_jointBottomSet_exit_mem_paths {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) {u v : Site 2}
    (hu : u ∈ rlc_jointBottomSet gamma delta)
    (hvR : v ∈ rect 0 (2 * n) (-n) n)
    (hadj : (hypercubicLattice 2).Adj u v)
    (hv : v ∉ rlc_jointBottomSet gamma delta) :
    v ∈ rlc_pathVertices gamma.1 ∨ v ∈ rlc_pathVertices delta.1 := by
  rcases hu with ⟨x, hxBottom, hxGamma, hxDelta, ⟨w⟩⟩
  have huData := rlc_rightPairAvoidGraph_walk_dest gamma delta
    hxBottom.1 hxGamma hxDelta w
  by_contra hvPath
  rw [not_or] at hvPath
  have hstep : (rlc_rightPairAvoidGraph gamma delta).Adj u v :=
    ⟨hadj, huData.1, hvR, huData.2.1, hvPath.1,
      huData.2.2, hvPath.2⟩
  exact hv ⟨x, hxBottom, hxGamma, hxDelta, ⟨w.concat hstep⟩⟩


theorem rlc_jointBottomSet_boundary_trace_safe {n : ℤ} (hn : 0 < n)
    (gamma delta : RlcRightDiagonalPath n) {u v : Site 2}
    (hu : u ∈ rlc_jointBottomSet gamma delta)
    (hvR : v ∈ rect 0 (2 * n) (-n) n)
    (hadj : (hypercubicLattice 2).Adj u v)
    (hvPath : v ∈ rlc_pathVertices gamma.1 ∨
      v ∈ rlc_pathVertices delta.1) :
    v ∉ rlc_rightUpperUnionSet gamma delta := by
  have huBelow := rlc_jointBottomSet_subset_commonStrictBelowSet
    gamma delta hu
  intro hvTop
  rcases hvTop with hvTopGamma | hvTopDelta
  · rcases hvPath with hvGamma | hvDelta
    · exact (Set.disjoint_left.mp
        (rlc_strictTopSet_disjoint_path gamma)) hvTopGamma hvGamma
    · have hvNotGamma : v ∉ rlc_pathVertices gamma.1 := by
        intro hvGamma
        exact (Set.disjoint_left.mp
          (rlc_strictTopSet_disjoint_path gamma)) hvTopGamma hvGamma
      have hvBelowGamma := rlc_strictBelowSet_step gamma huBelow.1
        hvR hvNotGamma hadj
      exact (Set.disjoint_left.mp
        (rlc_strictTopSet_disjoint_strictBelowSet hn gamma))
          hvTopGamma hvBelowGamma
  · rcases hvPath with hvGamma | hvDelta
    · have hvNotDelta : v ∉ rlc_pathVertices delta.1 := by
        intro hvDelta
        exact (Set.disjoint_left.mp
          (rlc_strictTopSet_disjoint_path delta)) hvTopDelta hvDelta
      have hvBelowDelta := rlc_strictBelowSet_step delta huBelow.2
        hvR hvNotDelta hadj
      exact (Set.disjoint_left.mp
        (rlc_strictTopSet_disjoint_strictBelowSet hn delta))
          hvTopDelta hvBelowDelta
    · exact (Set.disjoint_left.mp
        (rlc_strictTopSet_disjoint_path delta)) hvTopDelta hvDelta


theorem rlc_jointBottomSet_exit_mem_paths_and_safe {n : ℤ} (hn : 0 < n)
    (gamma delta : RlcRightDiagonalPath n) {u v : Site 2}
    (hu : u ∈ rlc_jointBottomSet gamma delta)
    (hvR : v ∈ rect 0 (2 * n) (-n) n)
    (hadj : (hypercubicLattice 2).Adj u v)
    (hv : v ∉ rlc_jointBottomSet gamma delta) :
    (v ∈ rlc_pathVertices gamma.1 ∨
      v ∈ rlc_pathVertices delta.1) ∧
      v ∉ rlc_rightUpperUnionSet gamma delta := by
  have hvPath := rlc_jointBottomSet_exit_mem_paths
    gamma delta hu hvR hadj hv
  exact ⟨hvPath, rlc_jointBottomSet_boundary_trace_safe
    hn gamma delta hu hvR hadj hvPath⟩


end Universality
end StatMech

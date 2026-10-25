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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part39
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_rot180_mem_strictTop_of_mem_strictBottom {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) {z : Site 2}
    (hz : z ∈ rlc_strictBottomSet gamma) :
    rlc_rot180 z ∈ rlc_strictTopSet (rlc_rot180LeftPath gamma) := by
  obtain ⟨x, hxBottom, hxPath, hreach⟩ := hz
  obtain ⟨w⟩ := hreach
  have hxTop : rlc_rot180 x ∈ topSide 0 (2 * n) (-n) n := by
    rw [mem_topSide]
    rw [mem_bottomSide] at hxBottom
    refine ⟨(rlc_rot180_mem_leftRect_iff_rightRect n x).mp hxBottom.1, ?_⟩
    simp only [rlc_rot180_one, hxBottom.2]
    omega
  have hxNot : rlc_rot180 x ∉
      rlc_pathVertices (rlc_rot180LeftPath gamma).1 := by
    intro hx
    rw [rlc_pathVertices_rot180LeftPath, Finset.mem_image] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := rlc_rot180.injective (by simpa using hyx)
    exact hxPath (this ▸ hy)
  exact ⟨rlc_rot180 x, hxTop, hxNot,
    ⟨w.map (rlc_rot180LeftAvoidHom gamma)⟩⟩

theorem rlc_rot180_mem_strictBottom_iff_mem_strictTop {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (z : Site 2) :
    rlc_rot180 z ∈ rlc_strictBottomSet (rlc_rot180RightPath gamma) ↔
      z ∈ rlc_strictTopSet gamma := by
  constructor
  · intro hz
    have hdouble := rlc_rot180_mem_strictTop_of_mem_strictBottom
      (rlc_rot180RightPath gamma) hz
    have heq := rlc_strictTopSet_eq_of_pathVertices_eq
      (rlc_rot180LeftPath (rlc_rot180RightPath gamma)) gamma
      (rlc_pathVertices_rot180_roundtrip_right gamma)
    rw [heq] at hdouble
    simpa using hdouble
  · exact rlc_rot180_mem_strictBottom_of_mem_strictTop gamma

theorem rlc_rot180_mem_strictTop_iff_mem_strictBottom {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) (z : Site 2) :
    rlc_rot180 z ∈ rlc_strictTopSet (rlc_rot180LeftPath gamma) ↔
      z ∈ rlc_strictBottomSet gamma := by
  constructor
  · intro hz
    have hdouble := rlc_rot180_mem_strictBottom_of_mem_strictTop
      (rlc_rot180LeftPath gamma) hz
    have heq := rlc_strictBottomSet_eq_of_pathVertices_eq
      (rlc_rot180RightPath (rlc_rot180LeftPath gamma)) gamma
      (rlc_pathVertices_rot180_roundtrip_left gamma)
    rw [heq] at hdouble
    simpa using hdouble
  · exact rlc_rot180_mem_strictTop_of_mem_strictBottom gamma

theorem rlc_strictBottomSet_mono_of_disjoint_path {n : ℤ}
    (gamma lambda : RlcLeftDiagonalPath n)
    (hdisj : Disjoint (rlc_strictBottomSet gamma)
      (rlc_pathVertices lambda.1 : Set (Site 2))) :
    rlc_strictBottomSet gamma ⊆ rlc_strictBottomSet lambda := by
  rintro z hz
  obtain ⟨x, hxBottom, hxGamma, hreach⟩ := hz
  have hxMem : x ∈ rlc_strictBottomSet gamma :=
    ⟨x, hxBottom, hxGamma, SimpleGraph.Reachable.refl x⟩
  have hxLambda : x ∉ rlc_pathVertices lambda.1 := fun hx =>
    (Set.disjoint_left.mp hdisj) hxMem hx
  obtain ⟨w⟩ := hreach
  have lift_walk : ∀ {a b : Site 2}
      (q : (rlc_leftPathAvoidGraph gamma).Walk a b),
      a ∈ rlc_strictBottomSet gamma →
      (rlc_leftPathAvoidGraph lambda).Walk a b := by
    intro a b q haBottom
    induction q with
    | nil => exact .nil
    | @cons a b c hab q ih =>
        have hbBottom := rlc_strictBottomSet_step gamma haBottom hab.2.2.1
          hab.2.2.2.2 hab.1
        have haLambda : a ∉ rlc_pathVertices lambda.1 := fun ha =>
          (Set.disjoint_left.mp hdisj) haBottom ha
        have hbLambda : b ∉ rlc_pathVertices lambda.1 := fun hb =>
          (Set.disjoint_left.mp hdisj) hbBottom hb
        exact .cons
          ⟨hab.1, (rlc_strictBottomSet_subset_box gamma haBottom), hab.2.2.1,
            haLambda, hbLambda⟩
          (ih hbBottom)
  exact ⟨x, hxBottom, hxLambda, ⟨lift_walk w hxMem⟩⟩


end Universality
end StatMech

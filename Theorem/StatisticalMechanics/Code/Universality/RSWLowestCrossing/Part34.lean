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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part33
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_strictTopSet_subset_box {n : ℤ}
    (gamma : RlcRightDiagonalPath n) :
    rlc_strictTopSet gamma ⊆ rect 0 (2 * n) (-n) n := by
  rintro z ⟨x, hxTop, hxP, hreach⟩
  obtain ⟨w⟩ := hreach
  exact (rlc_rightPathAvoidGraph_walk_dest gamma hxTop.1 hxP w).1

theorem rlc_strictTopSet_disjoint_path {n : ℤ}
    (gamma : RlcRightDiagonalPath n) :
    Disjoint (rlc_strictTopSet gamma)
      (rlc_pathVertices gamma.1 : Set (Site 2)) := by
  rw [Set.disjoint_left]
  rintro z ⟨x, hxTop, hxP, hreach⟩ hzPath
  obtain ⟨w⟩ := hreach
  exact (rlc_rightPathAvoidGraph_walk_dest gamma hxTop.1 hxP w).2 hzPath

theorem rlc_strictTopSet_step {n : ℤ}
    (gamma : RlcRightDiagonalPath n) {u v : Site 2}
    (hu : u ∈ rlc_strictTopSet gamma)
    (hvR : v ∈ rect 0 (2 * n) (-n) n)
    (hvp : v ∉ rlc_pathVertices gamma.1)
    (hadj : (hypercubicLattice 2).Adj u v) :
    v ∈ rlc_strictTopSet gamma := by
  obtain ⟨x, hxTop, hxPath, huv⟩ := hu
  obtain ⟨w⟩ := huv
  have huData := rlc_rightPathAvoidGraph_walk_dest gamma hxTop.1 hxPath w
  have hstep : (rlc_rightPathAvoidGraph gamma).Adj u v :=
    ⟨hadj, huData.1, hvR, huData.2, hvp⟩
  exact ⟨x, hxTop, hxPath, ⟨w.concat hstep⟩⟩

theorem rlc_strictTopSet_boundary_path {n : ℤ}
    (gamma : RlcRightDiagonalPath n) {u v : Site 2}
    (huR : u ∈ rect 0 (2 * n) (-n) n)
    (hvR : v ∈ rect 0 (2 * n) (-n) n)
    (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (rlc_strictTopSet gamma) s(u, v)) :
    u ∈ rlc_pathVertices gamma.1 ∨ v ∈ rlc_pathVertices gamma.1 := by
  rw [bdEdge_mk] at hbd
  by_cases hu : u ∈ rlc_strictTopSet gamma
  · right
    by_contra hvp
    exact (hbd.mp hu) (rlc_strictTopSet_step gamma hu hvR hvp hadj)
  · left
    by_contra hup
    have hv : v ∈ rlc_strictTopSet gamma := by
      by_contra hv
      exact hu (hbd.mpr hv)
    exact hu (rlc_strictTopSet_step gamma hv huR hup hadj.symm)


theorem rlc_strictTopSet_mono_of_disjoint_path {n : ℤ}
    (gamma lambda : RlcRightDiagonalPath n)
    (hdisj : Disjoint (rlc_strictTopSet gamma)
      (rlc_pathVertices lambda.1 : Set (Site 2))) :
    rlc_strictTopSet gamma ⊆ rlc_strictTopSet lambda := by
  rintro z hz
  obtain ⟨x, hxTop, hxGamma, hreach⟩ := hz
  have hxMem : x ∈ rlc_strictTopSet gamma :=
    ⟨x, hxTop, hxGamma, SimpleGraph.Reachable.refl x⟩
  have hxLambda : x ∉ rlc_pathVertices lambda.1 := fun hx =>
    (Set.disjoint_left.mp hdisj) hxMem hx
  obtain ⟨w⟩ := hreach
  have lift_walk : ∀ {a b : Site 2}
      (q : (rlc_rightPathAvoidGraph gamma).Walk a b),
      a ∈ rlc_strictTopSet gamma →
      (rlc_rightPathAvoidGraph lambda).Walk a b := by
    intro a b q haTop
    induction q with
    | nil => exact .nil
    | @cons a b c hab q ih =>
        have hbTop := rlc_strictTopSet_step gamma haTop hab.2.2.1
          hab.2.2.2.2 hab.1
        have haLambda : a ∉ rlc_pathVertices lambda.1 := fun ha =>
          (Set.disjoint_left.mp hdisj) haTop ha
        have hbLambda : b ∉ rlc_pathVertices lambda.1 := fun hb =>
          (Set.disjoint_left.mp hdisj) hbTop hb
        exact .cons
          ⟨hab.1, (rlc_strictTopSet_subset_box gamma haTop), hab.2.2.1,
            haLambda, hbLambda⟩
          (ih hbTop)
  exact ⟨x, hxTop, hxLambda, ⟨lift_walk w hxMem⟩⟩


end Universality
end StatMech

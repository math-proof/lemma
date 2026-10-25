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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part40
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_strictAboveSet_subset_box {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) :
    rlc_strictAboveSet gamma ⊆ rect (-2 * n) 0 (-n) n := by
  rintro z ⟨x, hxTop, hxP, hreach⟩
  obtain ⟨w⟩ := hreach
  exact (rlc_leftPathAvoidGraph_walk_dest gamma hxTop.1 hxP w).1

theorem rlc_strictAboveSet_disjoint_path {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) :
    Disjoint (rlc_strictAboveSet gamma) (rlc_pathVertices gamma.1 : Set (Site 2)) := by
  rw [Set.disjoint_left]
  rintro z ⟨x, hxTop, hxP, hreach⟩ hzPath
  obtain ⟨w⟩ := hreach
  exact (rlc_leftPathAvoidGraph_walk_dest gamma hxTop.1 hxP w).2 hzPath

theorem rlc_strictAboveSet_step {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) {u v : Site 2}
    (hu : u ∈ rlc_strictAboveSet gamma)
    (hvR : v ∈ rect (-2 * n) 0 (-n) n)
    (hvp : v ∉ rlc_pathVertices gamma.1)
    (hadj : (hypercubicLattice 2).Adj u v) :
    v ∈ rlc_strictAboveSet gamma := by
  obtain ⟨x, hxTop, hxPath, huv⟩ := hu
  obtain ⟨w⟩ := huv
  have huData := rlc_leftPathAvoidGraph_walk_dest gamma hxTop.1 hxPath w
  have hstep : (rlc_leftPathAvoidGraph gamma).Adj u v :=
    ⟨hadj, huData.1, hvR, huData.2, hvp⟩
  exact ⟨x, hxTop, hxPath, ⟨w.concat hstep⟩⟩


theorem rlc_strictAboveSet_boundary_path {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) {u v : Site 2}
    (huR : u ∈ rect (-2 * n) 0 (-n) n)
    (hvR : v ∈ rect (-2 * n) 0 (-n) n)
    (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (rlc_strictAboveSet gamma) s(u, v)) :
    u ∈ rlc_pathVertices gamma.1 ∨ v ∈ rlc_pathVertices gamma.1 := by
  rw [bdEdge_mk] at hbd
  by_cases hu : u ∈ rlc_strictAboveSet gamma
  · right
    by_contra hvp
    exact (hbd.mp hu) (rlc_strictAboveSet_step gamma hu hvR hvp hadj)
  · left
    by_contra hup
    have hv : v ∈ rlc_strictAboveSet gamma := by
      by_contra hv
      exact hu (hbd.mpr hv)
    exact hu (rlc_strictAboveSet_step gamma hv huR hup hadj.symm)

end Universality
end StatMech

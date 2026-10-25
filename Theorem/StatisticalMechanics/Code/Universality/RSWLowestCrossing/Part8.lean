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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part8
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_pathOpen_dependsOn {a b c d : ℤ} (gamma : RlcCrossingPath a b c d) :
    DependsOn ((rlc_pathOpen gamma).indicator (fun _ => (1 : ℝ)))
      (rlc_pathEdges gamma : Set (Sym2 (Site 2))) := by
  intro omega omega' hagree
  have hiff : omega ∈ rlc_pathOpen gamma ↔ omega' ∈ rlc_pathOpen gamma := by
    constructor
    · intro h e he
      rw [← hagree e he]
      exact h e he
    · intro h e he
      rw [hagree e he]
      exact h e he
  by_cases hmem : omega ∈ rlc_pathOpen gamma
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hiff.mp hmem)]
  · rw [Set.indicator_of_notMem hmem,
      Set.indicator_of_notMem (fun h => hmem (hiff.mpr h))]

theorem rlc_pathOpen_measurableSet {a b c d : ℤ} (gamma : RlcCrossingPath a b c d) :
    MeasurableSet (rlc_pathOpen gamma) :=
  measurableSet_of_dependsOn (rlc_pathOpen_dependsOn gamma)


theorem rlc_edges_mapLe_eq {V : Type*} {G G' : SimpleGraph V} (h : G ≤ G')
    {u v : V} (w : G.Walk u v) : (w.mapLe h).edges = w.edges := by
  induction w with
  | nil => rfl
  | cons huv w ih => simp [SimpleGraph.Walk.mapLe, ih]


end Universality
end StatMech

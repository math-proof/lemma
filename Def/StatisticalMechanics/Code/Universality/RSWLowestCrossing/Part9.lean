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
import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part8
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


noncomputable def rlc_openWalkOfEdges {a b c d : ℤ}
    (omega : ConfigSpace (Sym2 (Site 2))) {u v : rect a b c d}
    (w : ((hypercubicLattice 2).induce (rect a b c d)).Walk u v)
    (hopen : ∀ e ∈ w.edges.toFinset.image (Sym2.map Subtype.val),
      omega e = true) :
    (openSubgraphInduce 2 omega (rect a b c d)).Walk u v := by
  induction w with
  | nil => exact .nil
  | @cons u v z huv w ih =>
    apply SimpleGraph.Walk.cons
    · rw [openSubgraphInduce_adj, openSubgraph_adj]
      constructor
      · exact huv
      · apply hopen
        simp
    · apply ih
      intro e he
      apply hopen
      simp only [SimpleGraph.Walk.edges_cons, List.toFinset_cons,
        Finset.image_insert, Finset.mem_insert]
      exact Or.inr he


end Universality
end StatMech

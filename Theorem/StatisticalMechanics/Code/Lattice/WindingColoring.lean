/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingColoring.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
import Theorem.StatisticalMechanics.Code.Lattice.BdEdgeMatchStarHull
import Def.StatisticalMechanics.Code.Lattice.WindingColoring
open SimpleGraph Set


namespace StatMech

namespace Lattice

@[simp] theorem wcl_flipCount_nil (flip : Site 2 → Site 2 → Prop) (x : Site 2) :
    wcl_flipCount flip (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk x x) = 0 := by
  classical
  simp [wcl_flipCount]

open Classical in


theorem wcl_flipCount_cons (flip : Site 2 → Site 2 → Prop) {a b c : Site 2}
    (hab : (hypercubicLattice 2).Adj a b) (p : (hypercubicLattice 2).Walk b c) :
    wcl_flipCount flip (Walk.cons hab p) =
      (if (flip a b ∨ flip b a) then 1 else 0) + wcl_flipCount flip p := by
  classical
  rw [wcl_flipCount, wcl_flipCount, SimpleGraph.Walk.edges_cons, List.countP_cons]
  by_cases h : (flip a b ∨ flip b a)
  · rw [if_pos (by simp only [Sym2.lift_mk, decide_eq_true_eq]; exact h), if_pos h]; ring
  · rw [if_neg (by simp only [Sym2.lift_mk, decide_eq_true_eq]; exact h), if_neg h]; ring


theorem wcl_flipCount_append (flip : Site 2 → Site 2 → Prop) {x y z : Site 2}
    (p : (hypercubicLattice 2).Walk x y) (q : (hypercubicLattice 2).Walk y z) :
    wcl_flipCount flip (p.append q) = wcl_flipCount flip p + wcl_flipCount flip q := by
  classical
  rw [wcl_flipCount, wcl_flipCount, wcl_flipCount, SimpleGraph.Walk.edges_append,
    List.countP_append]


theorem wcl_flipCount_reverse (flip : Site 2 → Site 2 → Prop) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) :
    wcl_flipCount flip w.reverse = wcl_flipCount flip w := by
  classical
  rw [wcl_flipCount, wcl_flipCount, SimpleGraph.Walk.edges_reverse, List.countP_reverse]


end Lattice
end StatMech

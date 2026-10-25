/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyCorrect.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanBridgeCycle.Part10
import Def.StatisticalMechanics.Code.Lattice.WhitneyCorrect
open SimpleGraph Set


namespace StatMech

namespace Lattice

@[simp] theorem whc_dualCross_nil (H : SimpleGraph (Site 2)) (x : Site 2) :
    whc_dualCross H (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk x x) = 0 := by
  classical
  simp [whc_dualCross]

open Classical in

theorem whc_dualCross_cons (H : SimpleGraph (Site 2)) {a b c : Site 2}
    (hab : (hypercubicLattice 2).Adj a b) (p : (hypercubicLattice 2).Walk b c) :
    whc_dualCross H (Walk.cons hab p) =
      (if whc_isCross H a b then 1 else 0) + whc_dualCross H p := by
  rw [whc_dualCross, whc_dualCross, SimpleGraph.Walk.edges_cons, List.countP_cons]
  by_cases h : whc_isCross H a b
  · rw [if_pos (by simp only [Sym2.lift_mk, decide_eq_true_eq]; exact h), if_pos h]; ring
  · rw [if_neg (by simp only [Sym2.lift_mk, decide_eq_true_eq]; exact h), if_neg h]; ring


end Lattice
end StatMech

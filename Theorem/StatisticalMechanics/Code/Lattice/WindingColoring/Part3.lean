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
import Def.StatisticalMechanics.Code.Lattice.WindingColoring.Part3
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem wcl_windingColoring_eq_of_walk (flip : Site 2 → Site 2 → Prop)
    (hce : wcl_ClosedEven flip) (o : Site 2) {f : Site 2}
    (w : (hypercubicLattice 2).Walk o f) :
    wcl_windingColoring flip o f ↔ Odd (wcl_flipCount flip w) := by
  unfold wcl_windingColoring
  rw [Nat.odd_iff, Nat.odd_iff,
    wcl_flipCount_parity_eq_of_closedEven flip hce (wcl_chosenWalk o f) w]


theorem wcl_windingColoring_compat (flip : Site 2 → Site 2 → Prop)
    (hsymm : wcl_SymmFlip flip) (hce : wcl_ClosedEven flip) (o : Site 2) {a b : Site 2}
    (hab : (hypercubicLattice 2).Adj a b) :
    (flip a b ↔
      (wcl_windingColoring flip o a ↔ ¬ wcl_windingColoring flip o b)) := by
  classical
  
  set wa := wcl_chosenWalk o a with hwa
  have hA : wcl_windingColoring flip o a ↔ Odd (wcl_flipCount flip wa) := Iff.rfl
  have hB : wcl_windingColoring flip o b ↔ Odd (wcl_flipCount flip (wa.concat hab)) :=
    wcl_windingColoring_eq_of_walk flip hce o (wa.concat hab)
  
  have hconcat : wcl_flipCount flip (wa.concat hab) =
      wcl_flipCount flip wa + (if (flip a b ∨ flip b a) then 1 else 0) := by
    rw [SimpleGraph.Walk.concat_eq_append, wcl_flipCount_append]
    congr 1
    show wcl_flipCount flip (SimpleGraph.Walk.cons hab SimpleGraph.Walk.nil) = _
    rw [wcl_flipCount_cons, wcl_flipCount_nil, add_zero]
  have hor : (flip a b ∨ flip b a) ↔ flip a b := by
    have := hsymm a b hab; tauto
  rw [hB, hconcat, hA]
  by_cases h : flip a b
  · rw [if_pos (hor.mpr h), Nat.odd_add_one]
    simp only [h, Nat.not_odd_iff_even, Nat.not_even_iff_odd]
  · rw [if_neg (fun hh => h (hor.mp hh)), add_zero]
    simp only [h, false_iff, not_iff]


end Lattice
end StatMech

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanStripInduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Universality.HVIntersection.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ArcSides.Part3
import Theorem.StatisticalMechanics.Code.Lattice.TwoPathsCrossWinding.Part2
import Def.StatisticalMechanics.Code.Lattice.JordanStripInduction
open Set SimpleGraph MeasureTheory


namespace StatMech

namespace Lattice

open StatMech.RSW.Box

open StatMech.Universality


@[simp] theorem jsi_cell_0 (k r : ℤ) : jsi_cell k r 0 = k := rfl

@[simp] theorem jsi_cell_1 (k r : ℤ) : jsi_cell k r 1 = r := rfl


theorem jsi_cell_eq (k r k' r' : ℤ) : jsi_cell k r = jsi_cell k' r' ↔ k = k' ∧ r = r' := by
  constructor
  · intro h
    exact ⟨by have := congrFun h 0; simpa using this, by have := congrFun h 1; simpa using this⟩
  · rintro ⟨h1, h2⟩; rw [h1, h2]


@[simp] theorem jsi_cell_mem_rect (k r α β c d : ℤ) :
    jsi_cell k r ∈ rect α β c d ↔ α ≤ k ∧ k ≤ β ∧ c ≤ r ∧ r ≤ d := by
  simp [rect, jsi_cell]


theorem jsi_vstep_adj (k r : ℤ) : (hypercubicLattice 2).Adj (jsi_cell k r) (jsi_cell k (r + 1)) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [jsi_cell]


theorem jsi_hstep_adj (k k' r : ℤ) (h : k - k' = 1 ∨ k - k' = -1) :
    (hypercubicLattice 2).Adj (jsi_cell k r) (jsi_cell k' r) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [jsi_cell]; omega


end Lattice
end StatMech

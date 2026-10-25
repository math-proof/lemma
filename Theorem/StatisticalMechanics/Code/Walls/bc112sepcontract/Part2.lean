/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc112sepcontract.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc110globalforest
import Theorem.StatisticalMechanics.Code.Walls.bc106separated.Part3
import Def.StatisticalMechanics.Code.Walls.bc112sepcontract.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc112_leaf_coord0 (hd : 1 ≤ d) (y : Site d) (k : ℤ) :
    bc112_leaf hd y k ⟨0, hd⟩ = y ⟨0, hd⟩ + k := by
  simp [bc112_leaf]


theorem bc112_leaf_coord_ne (hd : 1 ≤ d) (y : Site d) (k : ℤ) {i : Fin d} (hi : i ≠ ⟨0, hd⟩) :
    bc112_leaf hd y k i = y i := by
  simp [bc112_leaf, Function.update_of_ne hi]


theorem bc112_leaf_mem_box (hd : 1 ≤ d) {L : ℕ} (y : Site d) {k : ℤ} (hk : k.natAbs ≤ L) :
    bc112_leaf hd y k ∈ bc61_boxAround d L y := by
  rw [bc61_mem_boxAround, mem_box]
  intro i
  by_cases hi : i = ⟨0, hd⟩
  · subst hi
    have : (bc112_leaf hd y k - y) ⟨0, hd⟩ = k := by
      rw [Pi.sub_apply, bc112_leaf_coord0]; ring
    rw [this]; exact hk
  · have : (bc112_leaf hd y k - y) i = 0 := by
      rw [Pi.sub_apply, bc112_leaf_coord_ne hd y k hi, sub_self]
    rw [this]; simp


theorem bc112_leaf_inj (hd : 1 ≤ d) (y : Site d) {k k' : ℤ} (hkk : k ≠ k') :
    bc112_leaf hd y k ≠ bc112_leaf hd y k' := by
  intro h
  have := congrArg (fun f => f ⟨0, hd⟩) h
  simp only [bc112_leaf_coord0] at this
  omega


theorem bc112_leaf_ne_centre (hd : 1 ≤ d) (y : Site d) {k : ℤ} (hk : k ≠ 0) :
    bc112_leaf hd y k ≠ y := by
  intro h
  have := congrArg (fun f => f ⟨0, hd⟩) h
  simp only [bc112_leaf_coord0] at this
  omega


end StatMech.Walls

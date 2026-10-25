/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bktcuttransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bkfforest.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bkt_bot_reachable_iff {V : Type*} (t t' : V) :
    (⊥ : SimpleGraph V).Reachable t t' ↔ t = t' := by
  constructor
  · intro h
    obtain ⟨p⟩ := h
    cases p with
    | nil => rfl
    | cons hadj _ => exact absurd hadj (by simp)
  · rintro rfl; exact Reachable.refl _


end StatMech.Walls

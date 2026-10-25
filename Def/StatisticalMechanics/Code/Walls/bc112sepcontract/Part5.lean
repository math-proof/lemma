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
import Theorem.StatisticalMechanics.Code.Walls.bc112sepcontract.Part4
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


noncomputable def bc112_carrier (hd : 1 ≤ d) (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) :
    Finset (Site d) := by
  classical
  exact (bc112_hubs ω L R) ∪
    (bc112_hubs ω L R).biUnion (fun y => bc112_shifts.image (fun k => bc112_leaf hd y k))


def bc112_starRel (hd : 1 ≤ d) (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) :
    Site d → Site d → Prop :=
  fun u v => ∃ y ∈ bc112_hubs ω L R, ∃ k ∈ bc112_shifts,
    (u = y ∧ v = bc112_leaf hd y k) ∨ (v = y ∧ u = bc112_leaf hd y k)

end StatMech.Walls

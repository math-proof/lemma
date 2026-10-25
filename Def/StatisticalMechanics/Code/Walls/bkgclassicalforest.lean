/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkgclassicalforest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bgfacyclicstep
import Theorem.StatisticalMechanics.Code.Walls.bararmray
import Theorem.StatisticalMechanics.Code.Walls.bc69count.Part2
import Theorem.StatisticalMechanics.Code.Walls.bkwburtonkeane
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


def bkg_deleteVertex {V : Type*} (Amb : SimpleGraph V) (t : V) : SimpleGraph V where
  Adj a b := Amb.Adj a b ∧ a ≠ t ∧ b ≠ t
  symm := ⟨fun a b ⟨h, ha, hb⟩ => ⟨h.symm, hb, ha⟩⟩

end StatMech.Walls

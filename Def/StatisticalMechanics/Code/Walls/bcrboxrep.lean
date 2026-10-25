/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcrboxrep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.brtrouteclose
import Theorem.StatisticalMechanics.Code.Walls.btrtrifnotion.Part3
import Theorem.StatisticalMechanics.Code.Walls.bcrboxrep
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


def bcr_RepRoute (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d) (arm : Fin 3 → Site d) : Prop :=
  ∀ i j, i ≠ j → (bc67_contractedLattice ω L (arm j)).Reachable y (arm i)


open Classical in


noncomputable def bcr_cross : ConfigSpace (Sym2 (Site 2)) :=
  fun e => if (∃ k : ℤ, e = s(bc57_pt k 0, bc57_pt (k + 1) 0)) ∨
              (∃ h : ℤ, e = s(bc57_pt 0 h, bc57_pt 0 (h + 1))) then true else false


end StatMech.Walls

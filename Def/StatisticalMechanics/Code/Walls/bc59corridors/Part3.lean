/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc59corridors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc58wholebox.Part4
import Theorem.StatisticalMechanics.Code.Walls.bc49finiteenergy
import Theorem.StatisticalMechanics.Code.Walls.bc59corridors.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


def bc59_a1 : Site 2 := bc57_pt 1 0

def bc59_a2 : Site 2 := bc57_pt (-1) 0

def bc59_a3 : Site 2 := bc57_pt 0 1


noncomputable def bc59_G : Finset (Sym2 (Site 2)) :=
  {s((0 : Site 2), bc59_a1), s((0 : Site 2), bc59_a2), s((0 : Site 2), bc59_a3),
   s(bc57_pt 0 1, bc57_pt 0 2)}


noncomputable def bc59_omega' : ConfigSpace (Sym2 (Site 2)) :=
  forceOpenFinset bc59_G bc57_evenLines


end StatMech.Walls

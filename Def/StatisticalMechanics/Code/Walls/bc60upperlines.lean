/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc60upperlines.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc59corridors.Part3
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation


open Classical in


noncomputable def bc60_upperLines : ConfigSpace (Sym2 (Site 2)) :=
  fun e => if (∃ (k : ℤ) (h : ℤ), 1 ≤ h ∧ e = s(bc57_pt k h, bc57_pt (k + 1) h)) then true else false


end StatMech.Walls

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc57coarsetrif.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc56menger.Part4
import Theorem.StatisticalMechanics.Code.Walls.bc57coarsetrif.Part2
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation


open Classical in


noncomputable def bc57_evenLines : ConfigSpace (Sym2 (Site 2)) :=
  fun e => if (∃ k m : ℤ, e = s(bc57_pt k (2 * m), bc57_pt (k + 1) (2 * m))) then true else false


end StatMech.Walls

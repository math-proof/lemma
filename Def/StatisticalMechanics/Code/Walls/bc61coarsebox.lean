/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc61coarsebox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc60upperlines.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc54coarse
import Theorem.StatisticalMechanics.Code.Percolation.CanonForestCount
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


noncomputable def bc61_boxAround (d L : ℕ) (y : Site d) : Finset (Site d) := by
  classical
  exact ((box_finite d L).image (fun z => z + y)).toFinset


end StatMech.Walls

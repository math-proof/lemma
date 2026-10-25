/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf3armunion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bfkforestcount
import Theorem.StatisticalMechanics.Code.Walls.bgf3armunion
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


def bgf3_starRay : Fin 3 → ℕ → Fin 4 := fun j n => if n = 0 then 0 else (![1, 2, 3] : Fin 3 → Fin 4) j


def bgf3_starLen : Fin 3 → ℕ := fun _ => 1


end StatMech.Walls

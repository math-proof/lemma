/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc50arminjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc48classical.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc49finiteenergy
import Theorem.StatisticalMechanics.Code.Walls.bc50arminjection
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


def bc50_shadowArmEnd : Fin 2 → Fin 3 → Fin 5 :=
  fun _h i => match i with | 0 => 2 | 1 => 3 | 2 => 4


end StatMech.Walls

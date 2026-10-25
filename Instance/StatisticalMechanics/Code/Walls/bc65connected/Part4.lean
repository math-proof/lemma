/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc65connected.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc64coarseembed.Part5
import Theorem.StatisticalMechanics.Code.Percolation.CanonForestCount
import Def.StatisticalMechanics.Code.Walls.bc65connected.Part5
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


instance : DecidableRel bc65_cat3G.Adj := by unfold bc65_cat3G fromRel; intro a b; infer_instance


end StatMech.Walls

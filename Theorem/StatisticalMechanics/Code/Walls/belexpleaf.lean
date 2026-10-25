/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/belexpleaf.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bpeprobcount.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc120closure
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


theorem bel_measurableSet_edgeOpen (e : Sym2 (Site d)) :
    MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | ω e = true} :=
  measurableSet_eq_fun (StatMech.ConfigSpace.measurable_eval e) measurable_const


end StatMech.Walls

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/baoallopen.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bscsupercut.Part2
import Theorem.StatisticalMechanics.Code.Walls.bfcfaithful
import Theorem.StatisticalMechanics.Code.Walls.bgnglobalcontract.Part4
import Theorem.StatisticalMechanics.Code.Walls.baoallopen
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

noncomputable def bao_onlyBox0 (L : ℕ) : ConfigSpace (Sym2 (Site 2)) :=
  fun e => if e ∈ boxEdges 2 L then true else false


end StatMech.Walls

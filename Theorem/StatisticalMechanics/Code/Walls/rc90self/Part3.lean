/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc90self.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc89nested.Part3
import Def.StatisticalMechanics.Code.Walls.rc90self.Part3
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem rc90_Aself_not_complClosed : ¬ rc90_ComplClosed rc90_Aself := by
  intro h
  have hmem : (![false, false, false] : ConfigSpace (Fin 3)) ∈ rc90_Aself := by decide
  have := h _ hmem
  revert this
  decide


theorem rc90_self_diagonal_true_but_needs_injection :
    ¬ (rc80_disjOccG rc90_Aself rc90_Aself ⊆ rc80_reflInterG rc90_Aself rc90_Aself) := by
  decide


end StatMech.Walls

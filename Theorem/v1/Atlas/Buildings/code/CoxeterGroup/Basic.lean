/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/Basic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fintype.BigOperators
import Def.v1.Atlas.Buildings.code.CoxeterGroup.Basic
open Finset BigOperators


namespace CoxeterGroup

variable {B : Type*}

/-- Symmetry: $B_{s,t} = B_{t,s}$. -/
theorem formVal_symm (M : CoxeterMatrix B) (s t : B) :
    formVal M s t = formVal M t s := by
  simp only [formVal, M.symmetric s t]

/-- Diagonal value: $B_{s,s} = 1$. -/
theorem formVal_diag (M : CoxeterMatrix B) (s : B) :
    formVal M s s = 1 := by
  simp only [formVal, M.diagonal s]
  norm_num

end CoxeterGroup

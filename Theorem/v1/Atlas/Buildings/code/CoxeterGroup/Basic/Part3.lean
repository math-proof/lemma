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
import Def.v1.Atlas.Buildings.code.CoxeterGroup.Basic.Part3
open Finset BigOperators


namespace CoxeterGroup

variable {B : Type*}

variable [DecidableEq B] [Fintype B]

/-- The reflection $\sigma_s$ negates $e_s$: $\sigma_s(e_s) = -e_s$. -/
theorem sigma_e_self (M : CoxeterMatrix B) (s : B) :
    sigma M s (e s) = fun t => -(e s t) := by
  ext t
  simp only [sigma, bilinForm_e_e, formVal_diag]
  ring

end CoxeterGroup

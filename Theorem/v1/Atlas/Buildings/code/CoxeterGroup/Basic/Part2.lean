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
import Def.v1.Atlas.Buildings.code.CoxeterGroup.Basic.Part2
open Finset BigOperators


namespace CoxeterGroup

variable {B : Type*}

variable [DecidableEq B] [Fintype B]

/-- Evaluating the bilinear form on basis vectors recovers the matrix entry:
$B(e_s, e_t) = B_{s,t}$. -/
theorem bilinForm_e_e (M : CoxeterMatrix B) (s t : B) :
    bilinForm M (e s) (e t) = formVal M s t := by
  simp only [bilinForm, e]
  simp_rw [Pi.single_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  simp [Finset.sum_ite_eq']

end CoxeterGroup

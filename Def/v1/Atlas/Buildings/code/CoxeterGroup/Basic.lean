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
open Finset BigOperators


namespace CoxeterGroup

variable {B : Type*}

/-- Entry $B_{s,t}$ of the bilinear form on the geometric representation. -/
noncomputable def formVal (M : CoxeterMatrix B) (s t : B) : ℝ :=
  if M s t = 0 then -1
  else -Real.cos (Real.pi / (M s t : ℝ))

end CoxeterGroup

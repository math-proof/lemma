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
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.Basic.Part2
open Finset BigOperators


namespace CoxeterGroup

variable {B : Type*}

variable [DecidableEq B] [Fintype B]

/-- The reflection $\sigma_s$ on $\mathbb{R}^B$ associated to a simple generator
$s$: $\sigma_s(v) = v - 2\, B(v, e_s)\, e_s$. This is the simple reflection in
the geometric representation. -/
noncomputable def sigma (M : CoxeterMatrix B) (s : B) (v : B → ℝ) : B → ℝ :=
  fun t => v t - 2 * bilinForm M v (e s) * e s t

end CoxeterGroup

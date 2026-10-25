/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/SimpleGroups.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.AlgebraNotes.code.SimpleGroups


namespace SimpleGroups

open Matrix

open DualNumber in
structure IsOneParameterGroup (m : ℕ) (φ : ℝ → Matrix (Fin m) (Fin m) ℂ) : Prop where
  map_zero : φ 0 = 1
  map_add : ∀ s t : ℝ, φ (s + t) = φ s * φ t
  differentiable : Differentiable ℝ φ

end SimpleGroups

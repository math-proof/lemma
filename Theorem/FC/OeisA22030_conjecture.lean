/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA22030_conjecture.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.FC.OeisA22030_conjecture


namespace OeisA22030

@[simp] lemma b_zero : b 0 = 4 := rfl

@[simp] lemma b_one : b 1 = 16 := rfl

@[simp] lemma b_two : b 2 = 63 := rfl

@[simp] lemma b_three : b 3 = 249 := rfl

@[simp] lemma b_step (n : ℕ) :
    b (n + 4) = 4 * b (n + 3) - b (n + 1) + b n := by
  rw [b]


end OeisA22030

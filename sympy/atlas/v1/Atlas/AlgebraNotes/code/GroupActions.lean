/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/GroupActions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace GroupActions

open MulAction

variable {G : Type*} [Group G] {α : Type*} [MulAction G α]

def stabilizerSet (G : Type*) [Group G] [MulAction G α] (s : α) : Set G :=
  {g : G | g • s = s}

noncomputable def orbitEquivQuotientStabilizer (G : Type*) {α : Type*} [Group G]
    [MulAction G α] (s : α) :
    orbit G s ≃ G ⧸ stabilizer G s :=
  MulAction.orbitEquivQuotientStabilizer G s

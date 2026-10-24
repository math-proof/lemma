/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/SymmetricGroups.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.Group.Conj

open Equiv Equiv.Perm

namespace SymmetricGroups

variable {α : Type*} [Fintype α] [DecidableEq α]

def cycleType (σ : Perm α) : Multiset ℕ := σ.cycleType

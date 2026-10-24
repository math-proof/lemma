/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/SylowTheorems.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Dihedral

open Finset Nat MulAction Subgroup

namespace SylowTheorems

def IsSylowPSubgroup (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Finite G]
    (H : Subgroup G) : Prop :=
  Nat.card H = p ^ (Nat.card G).factorization p

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]

def poles (G : Type*) (X : Type*) [Group G] [MulAction G X] : Set X :=
  {x : X | ∃ g : G, g ≠ 1 ∧ g • x = x}

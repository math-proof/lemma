/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/BollobasTwoFamilies.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.Order.Field.Basic

open Finset Nat BigOperators

namespace BollobasTwoFamilies

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- `goodPerms S T` is the set of permutations `σ` of `α` such that every element of `S`
appears before every element of `T` in the linear ordering induced by `σ`. -/
noncomputable def goodPerms (S T : Finset α) : Finset (Equiv.Perm α) :=
  Finset.univ.filter (fun σ =>
    ∀ s ∈ S, ∀ t ∈ T, (Fintype.equivFin α (σ s) : ℕ) < (Fintype.equivFin α (σ t) : ℕ))

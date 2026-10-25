/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckModuleIrreducible.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
set_option maxHeartbeats 800000


/-- A combinatorial `ℤ₊`-ring on the basis `ι`: nonnegative structure constants `N`, a
distinguished set `I₀` whose sum is the unit, and associativity. -/
structure ZPlusRingIrr (ι : Type*) [DecidableEq ι] [Fintype ι] where
  N : ι → ι → ι → ℕ
  I₀ : Finset ι
  unit_mul : ∀ j k, ∑ s ∈ I₀, N s j k = if j = k then 1 else 0
  mul_unit : ∀ i k, ∑ s ∈ I₀, N i s k = if i = k then 1 else 0
  assoc : ∀ i j k l, ∑ m : ι, N i j m * N m k l = ∑ m : ι, N j k m * N i m l

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- A `ℤ₊`-module over a `ZPlusRingIrr`, indexed by a basis `κ`, with nonnegative action
constants compatible with the unit and with the multiplication of `R`. -/
structure ZPlusModuleIrr (R : ZPlusRingIrr ι) (κ : Type*) [DecidableEq κ] [Fintype κ] where
  act : ι → κ → κ → ℕ
  act_unit : ∀ l k, ∑ s ∈ R.I₀, act s l k = if l = k then 1 else 0
  act_compat : ∀ i j l k,
    ∑ m : ι, R.N i j m * act m l k = ∑ n : κ, act j l n * act i n k

variable {R : ZPlusRingIrr ι} {κ : Type*} [DecidableEq κ] [Fintype κ]

namespace ZPlusModuleIrr

variable (M : ZPlusModuleIrr R κ)

/-- A subset `S ⊆ κ` is a proper nontrivial `ℤ₊`-submodule of `M` if it is nonempty,
not all of `κ`, and closed under the action of every basis element of the ring. -/
structure IsZPlusSubmodule (S : Finset κ) : Prop where
  nonempty : S.Nonempty
  proper : S ≠ Finset.univ
  closed : ∀ (i : ι) (l : κ), l ∈ S → ∀ (k : κ), M.act i l k ≠ 0 → k ∈ S

end ZPlusModuleIrr

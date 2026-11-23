/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/BasedRings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.TensorCategories.code.GrothendieckRingCategorical.Part4
public import Theorem.Category.Atlas.v1.TensorCategories.code.GrothendieckRingCategorical
public import Theorem.Category.Atlas.v1.TensorCategories.code.GradedVec
public import Theorem.Category.Atlas.v1.TensorCategories.code.TannakaReconstruction
public import Theorem.v1.Atlas.TensorCategories.code.GradedVec.Part6
public import Structure.v1.Atlas.TensorCategories.code.TannakaReconstruction
public import Def.v1.Atlas.TensorCategories.code.BasedRings.Part2
public section

open Finset


/-- A multifusion ring (Definition 1.42.2(3)) is a based ring of finite rank. Encoded
as the full collection of structure constants `N`, the unit subset `I₀`, the duality
involution `star`, and the associativity, unit, and duality axioms, all stated over a
finite index type `ι`. -/
structure MultifusionRingDef (ι : Type*) [DecidableEq ι] [Fintype ι] where
  N : ι → ι → ι → ℕ
  I₀ : Finset ι
  star : ι → ι
  star_star : ∀ i, star (star i) = i
  assoc : ∀ i j k l, ∑ m : ι, N i j m * N m k l = ∑ m : ι, N j k m * N i m l
  sum_I₀_mul_left : ∀ j k, (∑ s ∈ I₀, N s j k) = if j = k then 1 else 0
  sum_I₀_mul_right : ∀ i k, (∑ s ∈ I₀, N i s k) = if i = k then 1 else 0
  duality_trace : ∀ i j, (∑ k ∈ I₀, N i j k) = if i = star j then 1 else 0
  star_anti : ∀ i j k, N i j k = N (star j) (star i) (star k)


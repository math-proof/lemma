/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/BasedRings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.TensorCategories.code.GrothendieckRingCategorical.Part4
public import Lemma.Category.Atlas.v1.TensorCategories.code.GrothendieckRingCategorical
public import Lemma.Category.Atlas.v1.TensorCategories.code.GradedVec
public import Theorem.Category.Atlas.v1.TensorCategories.code.TannakaReconstruction
public import Theorem.v1.Atlas.TensorCategories.code.GradedVec.Part6
public import Structure.v1.Atlas.TensorCategories.code.TannakaReconstruction
public import Def.v1.Atlas.TensorCategories.code.BasedRings
public section

open Finset


/-- The data of a based ring (Definition 1.42.2(1)): a `ℤ₊`-ring with an involution
`star : ι → ι` whose induced map `a ↦ a^*` is an anti-involution of the ring, such that
`τ(b_i b_j) = δ_{i, j^*}`. -/
structure BasedRingDef (ι : Type*) [DecidableEq ι] extends ZPlusRingDef ι where
  star : ι → ι
  star_star : ∀ i, star (star i) = i
  duality_trace : ∀ i j, (∑ k ∈ I₀, N i j k) = if i = star j then 1 else 0
  star_anti : ∀ i j k, N i j k = N (star j) (star i) (star k)


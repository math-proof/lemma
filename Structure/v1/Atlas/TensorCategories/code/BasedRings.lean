/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/BasedRings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.GrothendieckRingCategorical.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.GrothendieckRingCategorical
import Lemma.Category.Atlas.v1.TensorCategories.code.GradedVec
import Lemma.Category.Atlas.v1.TensorCategories.code.TannakaReconstruction
import Theorem.v1.Atlas.TensorCategories.code.GradedVec.Part6
import Structure.v1.Atlas.TensorCategories.code.TannakaReconstruction
open Finset


/-- The data of a `ℤ₊`-ring on a basis indexed by `ι`: structure constants
`N i j k`, a set `I₀ ⊂ ι` of unit basis elements, finiteness of the support of each
product, and associativity expressed via the finite sums of products of structure constants. -/
structure ZPlusRingDef (ι : Type*) [DecidableEq ι] where
  N : ι → ι → ι → ℕ
  I₀ : Finset ι
  finite_support : ∀ i j, Set.Finite {k | N i j k ≠ 0}
  sum_I₀_mul_left : ∀ j k, (∑ s ∈ I₀, N s j k) = if j = k then 1 else 0
  sum_I₀_mul_right : ∀ i k, (∑ s ∈ I₀, N i s k) = if i = k then 1 else 0
  assoc_finite : ∀ i j k l,
    Set.Finite {m | N i j m * N m k l ≠ 0} ∧
    Set.Finite {m | N j k m * N i m l ≠ 0} ∧
    ∑ᶠ m, N i j m * N m k l = ∑ᶠ m, N j k m * N i m l


/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckRingCategorical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TensorCategories.code.GrothendieckRing.Part2
import Lemma.Category.Atlas.v1.TensorCategories.code.GrothendieckRing
import Lemma.Category.Atlas.v1.TensorCategories.code.TensorCategoryDef
import Abbrev.v1.Atlas.TensorCategories.code.TensorCategoryDef.Part3
import Lemma.Category.Atlas.v1.TensorCategories.code.Prop_1_45_10
open CategoryTheory MonoidalCategory Limits Finset
open TensorCategories

universe v u


/-- Categorical fusion data for a `κ`-linear abelian rigid monoidal category `C`: a finite
indexing of representatives `S i` of simples, fusion coefficients `N`, duality involution,
and Jordan-Hölder multiplicities `mult` compatible with the unit, tensor product and
isomorphisms. -/
class CategoricalFusionData (κ : Type*) [Field κ] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear κ C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear κ C]
    [RigidCategory C] where
  ι : Type
  [ι_fintype : Fintype ι]
  [ι_deceq : DecidableEq ι]
  S : ι → C
  S_simple : ∀ i, Simple (S i)
  S_complete : ∀ (X : C), Simple X → ∃ i, Nonempty (X ≅ S i)
  S_distinct : ∀ i j, Nonempty (S i ≅ S j) → i = j
  unitIdx : ι
  unitIso : Nonempty (S unitIdx ≅ 𝟙_ C)
  N : ι → ι → ι → ℕ
  star : ι → ι
  star_star : ∀ i, star (star i) = i
  N_unit_mul : ∀ j k, N unitIdx j k = if j = k then 1 else 0
  N_mul_unit : ∀ i k, N i unitIdx k = if i = k then 1 else 0
  N_duality : ∀ i j, N i j unitIdx = if j = star i then 1 else 0
  N_assoc : ∀ i j m l, ∑ p : ι, N i j p * N p m l = ∑ p : ι, N j m p * N i p l
  N_star_transpose : ∀ i j k, N i j k = N (star i) k j
  N_eq_finrank : ∀ i j k, N i j k = Module.finrank κ (S k ⟶ (S i ⊗ S j))
  mult : C → ι → ℕ
  mult_simple : ∀ i j, mult (S i) j = if i = j then 1 else 0
  mult_unit : ∀ j, mult (𝟙_ C) j = if j = unitIdx then 1 else 0
  mult_tensor : ∀ (X Y : C) (l : ι),
    mult (X ⊗ Y) l = ∑ i : ι, ∑ j : ι, mult X i * mult Y j * N i j l
  mult_iso : ∀ (X Y : C), Nonempty (X ≅ Y) → ∀ i, mult X i = mult Y i
  mult_nontrivial : ∀ (X : C), ∃ i, 0 < mult X i


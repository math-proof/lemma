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
import Def.v1.Atlas.TensorCategories.code.BasedRings.Part3
open Finset


namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : FusionRing ι)

/-- An isomorphism of fusion rings: a bijection of bases compatible with the unit element,
the structure constants, and the duality involution. -/
structure FusionRingIso
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    (R : FusionRing ι) (S : FusionRing κ) where
  toEquiv : ι ≃ κ
  map_unit : toEquiv R.unit = S.unit
  map_N : ∀ i j k, R.N i j k = S.N (toEquiv i) (toEquiv j) (toEquiv k)
  map_star : ∀ i, toEquiv (R.star i) = S.star (toEquiv i)

/-- A categorification of a fusion ring `R` over a field `k`: a `k`-linear abelian rigid
monoidal category `C` together with an isomorphism between its Grothendieck fusion ring
and `R`. -/
structure Categorification.{u, v}
    {ι : Type*} [DecidableEq ι] [Fintype ι] (R : FusionRing ι)
    (k : Type*) [Field k] where
  C : Type u
  [cat : CategoryTheory.Category.{v} C]
  [preadditive : CategoryTheory.Preadditive C]
  [linear : CategoryTheory.Linear k C]
  [abelian : CategoryTheory.Abelian C]
  [monoidal : CategoryTheory.MonoidalCategory C]
  [monoidalPreadditive : CategoryTheory.MonoidalPreadditive C]
  [monoidalLinear : CategoryTheory.MonoidalLinear k C]
  [rigid : CategoryTheory.RigidCategory C]
  cfd : @CategoricalFusionData k _ C cat preadditive linear abelian monoidal
    monoidalPreadditive monoidalLinear rigid
  grIso : FusionRingIso (@CategoricalFusionData.toFusionRing k _ C cat preadditive
    linear abelian monoidal monoidalPreadditive monoidalLinear rigid cfd) R

end FusionRing

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_45_2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.GrothendieckRingCategorical.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.GrothendieckRingCategorical
open CategoryTheory MonoidalCategory

universe v u


/-- The fusion ring (Grothendieck ring) underlying the categorical fusion data on `C`,
provided as a packaged form of Proposition 1.45.2. -/
def Proposition_1_45_2_fusionRing
    {κ : Type*} [Field κ] {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear κ C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear κ C]
    [RigidCategory C]
    [cfd : CategoricalFusionData κ C] :
    FusionRing cfd.ι :=
  CategoricalFusionData.toFusionRing

/-- The ring instance on the Grothendieck ring of the categorical fusion data on `C`,
provided as part of Proposition 1.45.2. -/
def Proposition_1_45_2_ring_instance
    {κ : Type*} [Field κ] {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear κ C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear κ C]
    [RigidCategory C]
    [cfd : CategoricalFusionData κ C] :
    Ring (FusionRing.GrRingOf (CategoricalFusionData.toFusionRing (κ := κ) (C := C))) :=
  FusionRing.GrRingOf.instRing


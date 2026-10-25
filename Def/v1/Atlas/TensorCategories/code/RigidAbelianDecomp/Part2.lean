/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/RigidAbelianDecomp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TensorCategories.code.MacLaneCoherence
import Lemma.Category.Atlas.v1.TensorCategories.code.MacLaneCoherence
import Lemma.Category.Atlas.v1.TensorCategories.code.MacLaneStrictness
import Lemma.Category.Atlas.v1.TensorCategories.code.InvertibleObjects
import Lemma.Category.Atlas.v1.TensorCategories.code.TensorCategoryDef
import Lemma.Category.Atlas.v1.TensorCategories.code.TensorExact
import Lemma.Category.Atlas.v1.TensorCategories.code.GrothendieckRing
import Instance.v1.Atlas.TensorCategories.code.MacLaneStrictness.Part2
import Instance.v1.Atlas.TensorCategories.code.InvertibleObjects
import Abbrev.v1.Atlas.TensorCategories.code.TensorCategoryDef.Part3
import Def.v1.Atlas.TensorCategories.code.TensorExact.Part3
import Theorem.v1.Atlas.TensorCategories.code.GrothendieckRing.Part2
import Abbrev.v1.Atlas.TensorCategories.code.FiniteAbelianCategoryDef
import Abbrev.v1.Atlas.TensorCategories.code.RigidAbelianDecomp.Part2
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory


/-- The ring homomorphism between Grothendieck rings induced by a homomorphism of
fusion rings. -/
def grothendieckRing_induced_hom
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    {R : FusionRing ι} {S : FusionRing κ}
    (φ : FusionRing.FusionRingHom R S) :
    FusionRing.GrRingOf R →+* FusionRing.GrRingOf S :=
  φ.inducedRingHom


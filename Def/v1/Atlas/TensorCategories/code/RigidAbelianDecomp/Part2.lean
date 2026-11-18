/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/RigidAbelianDecomp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.TensorCategories.code.FrobeniusPerron
import Structure.v1.Atlas.TensorCategories.code.GrothendieckRing
import Structure.v1.Atlas.TensorCategories.code.GrothendieckRing.Part2
import Def.v1.Atlas.TensorCategories.code.GrothendieckRing.Part3
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

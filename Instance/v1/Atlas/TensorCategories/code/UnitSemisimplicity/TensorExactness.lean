/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/TensorExactness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TensorCategories.code.UnitSemisimplicity.MonoidalBiexact.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.UnitSemisimplicity.MonoidalBiexact
import Lemma.Category.Atlas.v1.TensorCategories.code.FittingLemmaInstance
import Instance.v1.Atlas.TensorCategories.code.FittingLemmaInstance
import Mathlib.Algebra.Group.Pi.Units
import Theorem.v1.Atlas.TensorCategories.code.UnitSemisimplicity.TensorExactness
open CategoryTheory MonoidalCategory Category CategoryTheory.Limits

universe v u w


noncomputable section

namespace TensorCategories

/-- Instance form of `unitIsSimple`, registering simplicity of `𝟙_ C` for typeclass
inference whenever an indecomposability hypothesis is supplied. -/
instance instSimpleUnitOfUnitIsSimple (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [Abelian C] [RightRigidCategory C] [LeftRigidCategory C] [MonoidalPreadditive C]
    [MonoidalBiexact C] [IsArtinianRing (End (𝟙_ C))] [IsArtinianObject (𝟙_ C)]
    (hIndecomp : Indecomposable (𝟙_ C)) : Simple (𝟙_ C) :=
  unitIsSimple C hIndecomp

end TensorCategories
end

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DistinguishedInvertible.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.CategoryTheory.Yoneda
import Instance.v1.Atlas.TensorCategories.code.InvertibleObjects
import Lemma.Category.Atlas.v1.TensorCategories.code.InvertibleObjects
import Lemma.Category.Atlas.v1.TensorCategories.code.PivotalSpherical
import Structure.v1.Atlas.TensorCategories.code.PivotalSpherical.Part3
import Def.v1.Atlas.TensorCategories.code.CategoricalFreeness.Part2
import Class.v1.Atlas.TensorCategories.code.DistinguishedInvertible.Part3
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category Limits TensorCategories

universe v u


namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]


/-- The monoidal unit `𝟙_C` is always an invertible object, with both inverses given by
the unit isomorphisms. -/
@[reducible]
def unitIsInvertibleObject
    (C : Type u) [Category.{v} C] [MonoidalCategory C] :
    IsInvertibleObject (𝟙_ C) where
  tensorInverse := 𝟙_ C
  compIso := λ_ (𝟙_ C)
  invCompIso := λ_ (𝟙_ C)

end CategoryTheory

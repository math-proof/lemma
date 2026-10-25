/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Definition_1_52_6.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
open CategoryTheory MonoidalCategory

universe u v


/-- Minimal data of a distinguished invertible object `L_ρ` in a rigid monoidal category
`C`, here packaged simply as the chosen object. -/
class HasDistinguishedInvertibleData (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [RigidCategory C] where
  distinguished : C

/-- A rigid monoidal category is unimodular when its distinguished invertible object
`L_ρ` is isomorphic to the unit object `𝟙_C`. -/
class IsUnimodularCategory' (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [RigidCategory C] [HasDistinguishedInvertibleData C] : Prop where
  distinguished_iso_unit :
    Nonempty (HasDistinguishedInvertibleData.distinguished (C := C) ≅ 𝟙_ C)


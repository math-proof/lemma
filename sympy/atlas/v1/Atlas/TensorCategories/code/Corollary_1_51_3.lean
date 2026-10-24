/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Corollary_1_51_3.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Yoneda
import sympy.atlas.v1.Atlas.TensorCategories.code.InvertibleObjects
import Lemma.Category.Atlas.v1.TensorCategories.code.InvertibleObjects

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category

universe v u

namespace CategoryTheory


section TensorDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

/-- The double right dual `(Xᘁ)ᘁ` of an object `X` in a rigid monoidal category. -/
def doubleDualObj (X : C) : C :=
  HasRightDual.rightDual (HasRightDual.rightDual X)

variable (C) in
/-- A choice of distinguished invertible object `L_ρ` in a rigid monoidal category `C`,
along with a proof that it is invertible. This is the categorical analogue of the
distinguished group-like element in a quasi-Hopf algebra (Section 1.51). -/
class HasDistinguishedInvData where
  distinguished : C
  invertible : IsInvertibleObject distinguished

variable [HasDistinguishedInvData C]

/-- The distinguished invertible object `L_ρ` of `C` supplied by `HasDistinguishedInvData`. -/
def distinguishedObj : C := HasDistinguishedInvData.distinguished (C := C)

/-- The distinguished object `L_ρ` is invertible. -/
instance distinguishedObj_invertible : IsInvertibleObject (distinguishedObj (C := C)) :=
  HasDistinguishedInvData.invertible (C := C)

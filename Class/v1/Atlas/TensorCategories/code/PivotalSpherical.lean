/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/PivotalSpherical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Abbrev.v1.Atlas.TensorCategories.code.PivotalSpherical
set_option maxHeartbeats 800000

set_option autoImplicit false

open CategoryTheory MonoidalCategory Category Limits

universe w v u


namespace TensorCategories

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

/-- Class form of `PivotalStructure`: a pivotal structure on a rigid monoidal category as
a typeclass for instance inference. -/
class PivotalCategory where
  pivotalIso : ∀ (V : C), V ≅ (Vᘁ)ᘁ
  tensorCoherenceIso : ∀ (V W : C), (Vᘁ)ᘁ ⊗ (Wᘁ)ᘁ ≅ ((V ⊗ W : C)ᘁ : C)ᘁ
  naturality : ∀ {V W : C} (f : V ⟶ W),
    f ≫ (pivotalIso W).hom = (pivotalIso V).hom ≫ (fᘁ)ᘁ
  monoidality : ∀ (V W : C),
    (pivotalIso (V ⊗ W)).hom =
      ((pivotalIso V).hom ⊗ₘ (pivotalIso W).hom) ≫ (tensorCoherenceIso V W).hom
  dimUnit : leftQuantumTrace C (pivotalIso (𝟙_ C)).hom = 𝟙 (𝟙_ C)

end TensorCategories

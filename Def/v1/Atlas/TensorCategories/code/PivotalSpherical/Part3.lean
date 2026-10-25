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
import Abbrev.v1.Atlas.TensorCategories.code.PivotalSpherical.Part2
set_option maxHeartbeats 800000

set_option autoImplicit false

open CategoryTheory MonoidalCategory Category Limits

universe w v u


namespace TensorCategories

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

section PivotalSection

variable [PivotalCategory C]

/-- Pivotal trace of an endomorphism `f : V ⟶ V`: the left quantum trace of `f` composed
with the pivotal isomorphism. -/
noncomputable def pivotalTrace {V : C} (f : V ⟶ V) : 𝟙_ C ⟶ 𝟙_ C :=
  leftQuantumTrace C (f ≫ (PivotalCategory.pivotalIso (C := C) V).hom)

/-- Alias for `pivotalTrace`: the categorical trace of an endomorphism. -/
noncomputable def categoricalTrace {V : C} (f : V ⟶ V) : 𝟙_ C ⟶ 𝟙_ C :=
  pivotalTrace C f

end PivotalSection
end TensorCategories

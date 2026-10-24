/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Definition_1_5_1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

open CategoryTheory MonoidalCategory

universe v₁ v₂ u₁ u₂

namespace TensorCategories

/-- Definition 1.5.1: A morphism (or natural transformation) of monoidal functors eta:
(F^1, J^1) → (F^2, J^2) is a natural transformation eta: F^1 → F^2 such that eta_1 is an
isomorphism and the diagram involving J^1, J^2, and eta is commutative for all X, Y in C.
This is an alias for Mathlib's `NatTrans.IsMonoidal`. -/
abbrev Definition_1_5_1 := @NatTrans.IsMonoidal

/-- Convenient alias `MonoidalNatTrans` for `NatTrans.IsMonoidal` matching the textbook
terminology of Definition 1.5.1. -/
abbrev MonoidalNatTrans := @NatTrans.IsMonoidal

/-- Lowercase alias for `Definition_1_5_1`. -/
abbrev def_1_5_1 := @NatTrans.IsMonoidal

section Conditions

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
variable {F₁ F₂ : C ⥤ D} [F₁.LaxMonoidal] [F₂.LaxMonoidal]
variable (η : F₁ ⟶ F₂) [NatTrans.IsMonoidal η]

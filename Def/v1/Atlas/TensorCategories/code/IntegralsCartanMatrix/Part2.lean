/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsCartanMatrix.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

@[expose] public section
set_option maxHeartbeats 400000

set_option autoImplicit false

open CategoryTheory MonoidalCategory

universe u v w


section CartanMatrix

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

/-- The left quantum trace of a morphism  : V ⟶ V**, defined as the composition
coev_V ≫ (a ▷ V*) ≫ ev_{V*} ending in 𝟙_ C ⟶ 𝟙_ C. -/
noncomputable def leftQuantumTrace' {V : C} (a : V ⟶ (Vᘁ)ᘁ) : 𝟙_ C ⟶ 𝟙_ C :=
  η_ V (Vᘁ) ≫ (a ▷ Vᘁ) ≫ ε_ (Vᘁ) ((Vᘁ)ᘁ)

end CartanMatrix

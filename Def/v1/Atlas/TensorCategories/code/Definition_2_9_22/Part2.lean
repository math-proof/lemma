/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Definition_2_9_22.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Monoidal.Mon_
public import Mathlib.CategoryTheory.Monoidal.Mod_
public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Abbrev.v1.Atlas.TensorCategories.code.Definition_2_9_22

@[expose] public section

set_option maxHeartbeats 400000

universe v u


namespace CategoryTheory

open Category MonoidalCategory MonObj Limits

section SimpleAndSemisimple

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- An algebra object `A ∈ C` is semisimple when its category of modules is
preadditive and every module decomposes as a biproduct of simple modules. -/
def IsSemisimpleAlgebra (A : C) [MonObj A] : Prop :=
  ∃ (hp : Preadditive (Mod_ C A)),
    let hz : HasZeroMorphisms (Mod_ C A) :=
      @Preadditive.preadditiveHasZeroMorphisms _ _ hp
    ∀ (X : Mod_ C A), ∃ (n : ℕ) (Y : Fin n → Mod_ C A)
      (_ : ∀ i, @Simple (Mod_ C A) _ hz (Y i))
      (_ : @HasBiproduct (Fin n) (Mod_ C A) _ hz Y),
      Nonempty (X ≅ @biproduct (Fin n) (Mod_ C A) _ hz Y _)

/-- An algebra object `A ∈ C` is simple when its category of modules has a unique
simple object up to isomorphism. -/
def IsSimpleAlgebra (A : C) [MonObj A] : Prop :=
  ∃ (hz : HasZeroMorphisms (Mod_ C A)) (S : Mod_ C A) (_ : @Simple (Mod_ C A) _ hz S),
    ∀ (X : Mod_ C A), @Simple (Mod_ C A) _ hz X → Nonempty (X ≅ S)

end SimpleAndSemisimple
end CategoryTheory

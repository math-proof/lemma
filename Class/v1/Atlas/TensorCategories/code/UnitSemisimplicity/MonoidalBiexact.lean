module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/MonoidalBiexact.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.Tactic.CategoryTheory.Monoidal.PureCoherence
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Preadditive.Schur
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.RingTheory.SimpleModule.WedderburnArtin
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.RingTheory.SimpleRing.Field
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.CategoryTheory.Subobject.ArtinianObject
public import Mathlib.RingTheory.Idempotents
public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.Tactic.CategoryTheory.Slice
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Theorem.v1.Atlas.TensorCategories.code.UnitSemisimplicity.MonoidalBiexact.Part2
public section
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category CategoryTheory.Limits

universe v u w


noncomputable section

namespace TensorCategories

/-- A monoidal abelian category is *monoidally biexact* if tensoring on either side
preserves monomorphisms and epimorphisms, and if `X ⊗ X` being zero forces `X` to be zero.
This abstracts Proposition 1.13.1 together with the nondegeneracy needed for the proof
that `End(𝟙)` is reduced. -/
class MonoidalBiexact (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [Abelian C] : Prop where
  whiskerRight_mono : ∀ {X Y : C} (f : X ⟶ Y) [Mono f] (Z : C), Mono (f ▷ Z)
  whiskerLeft_mono : ∀ (Z : C) {X Y : C} (f : X ⟶ Y) [Mono f], Mono (Z ◁ f)
  whiskerRight_epi : ∀ {X Y : C} (f : X ⟶ Y) [Epi f] (Z : C), Epi (f ▷ Z)
  whiskerLeft_epi : ∀ (Z : C) {X Y : C} (f : X ⟶ Y) [Epi f], Epi (Z ◁ f)
  isZero_of_tensorObj_self_isZero : ∀ (X : C), IsZero (X ⊗ X) → IsZero X

end TensorCategories
end

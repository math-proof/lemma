/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/MonoidalBiexact.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

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
public import Instance.v1.Atlas.TensorCategories.code.UnitSemisimplicity.MonoidalBiexact.Part2
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category CategoryTheory.Limits

public section

universe v u w


noncomputable section

namespace TensorCategories

section TensorNondegenProof

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
  [MonoidalPreadditive C] [RigidCategory C] [BraidedCategory C]

/-- In an abelian braided rigid monoidal category, if `X ⊗ X` is the zero object then
`X` itself is zero. The argument uses the zig-zag identity and duals to show that the
left unitor of `X` vanishes. -/
theorem isZero_of_tensorSelf_isZero (X : C) (h : IsZero (X ⊗ X)) : IsZero X := by

  have h1 : IsZero ((X ⊗ X) ⊗ HasRightDual.rightDual X) :=
    (tensorRight _).map_isZero h

  have h2 : IsZero (X ⊗ (X ⊗ HasRightDual.rightDual X)) :=
    h1.of_iso (α_ X X (HasRightDual.rightDual X)).symm


  have h3 : IsZero (X ⊗ (HasRightDual.rightDual X ⊗ X)) :=
    h2.of_iso ((tensorLeft X).mapIso (β_ (HasRightDual.rightDual X) X))

  have h4 : IsZero ((X ⊗ HasRightDual.rightDual X) ⊗ X) :=
    h3.of_iso (α_ X (HasRightDual.rightDual X) X)


  have hz : η_ X (HasRightDual.rightDual X) ▷ X = 0 :=
    h4.eq_of_tgt _ _


  have zigzag := ExactPairing.evaluation_coevaluation X (HasRightDual.rightDual X)

  rw [hz, zero_comp] at zigzag


  have hlam : (λ_ X).hom = 0 := by
    have : (λ_ X).hom = ((λ_ X).hom ≫ (ρ_ X).inv) ≫ (ρ_ X).hom := by simp
    rw [this, zigzag.symm, zero_comp]

  rw [IsZero.iff_id_eq_zero]
  calc 𝟙 X = (λ_ X).inv ≫ (λ_ X).hom := by simp
    _ = (λ_ X).inv ≫ 0 := by rw [hlam]
    _ = 0 := by simp

end TensorNondegenProof
end TensorCategories
end

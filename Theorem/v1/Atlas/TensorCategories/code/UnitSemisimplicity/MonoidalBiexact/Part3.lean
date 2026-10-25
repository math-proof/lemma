/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/MonoidalBiexact.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.Tactic.CategoryTheory.Monoidal.PureCoherence
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.RingTheory.SimpleRing.Field
import Mathlib.RingTheory.Artinian.Module
import Mathlib.CategoryTheory.Subobject.ArtinianObject
import Mathlib.RingTheory.Idempotents
import Mathlib.CategoryTheory.Idempotents.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.Tactic.CategoryTheory.Slice
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Instance.v1.Atlas.TensorCategories.code.UnitSemisimplicity.MonoidalBiexact.Part2
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category CategoryTheory.Limits

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

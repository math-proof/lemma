/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Lemma_2_9_12.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Mon_

set_option maxHeartbeats 400000

universe v u

namespace CategoryTheory

open Category MonoidalCategory MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

variable (A : C) [MonObj A]

/-- A right module structure on an object `M` over a monoid object `A` in a monoidal category,
consisting of an action morphism `M ⊗ A ⟶ M` compatible with the unit and multiplication of `A`. -/
structure RightModObj' (M : C) where
  act : M ⊗ A ⟶ M
  act_unit : (M ◁ η[A]) ≫ act = (ρ_ M).hom := by aesop_cat
  act_assoc : (act ▷ A) ≫ act = (α_ M A A).hom ≫ (M ◁ μ[A]) ≫ act := by aesop_cat

attribute [reassoc (attr := simp)] RightModObj'.act_unit RightModObj'.act_assoc

/-- A right `A`-module in `C`: an object `X` together with a right `A`-module structure on it. -/
structure RightMod' where
  X : C
  mod : RightModObj' A X

variable {A}

/-- A morphism of right `A`-modules: a morphism between underlying objects that intertwines
the right `A`-action. -/
@[ext]
structure RightMod'.Hom (M N : RightMod' A) where
  hom : M.X ⟶ N.X
  comm : M.mod.act ≫ hom = (hom ▷ A) ≫ N.mod.act := by aesop_cat

attribute [reassoc (attr := simp)] RightMod'.Hom.comm

namespace RightMod'

/-- The regular right `A`-module: `A` itself with action given by multiplication `μ[A]`. -/
@[simps]
def regular (A : C) [MonObj A] : RightMod' (A := A) where
  X := A
  mod := { act := μ[A] }

/-- The right `A`-module structure on `X ⊗ M.X` induced from a right `A`-module `M`, where
`A` acts on the right factor via the associator. -/
def tensorModObj (X : C) (M : RightMod' A) : RightModObj' A (X ⊗ M.X) where
  act := (α_ X M.X A).hom ≫ X ◁ M.mod.act
  act_unit := by
    calc (X ⊗ M.X) ◁ η ≫ (α_ X M.X A).hom ≫ X ◁ M.mod.act
        = (α_ X M.X _).hom ≫ X ◁ (M.X ◁ η) ≫ X ◁ M.mod.act := by simp [assoc]
      _ = (α_ X M.X _).hom ≫ X ◁ ((M.X ◁ η) ≫ M.mod.act) := by rw [whiskerLeft_comp]
      _ = (α_ X M.X _).hom ≫ X ◁ (ρ_ M.X).hom := by rw [M.mod.act_unit]
      _ = (ρ_ (X ⊗ M.X)).hom := (rightUnitor_tensor_hom X M.X).symm
  act_assoc := by
    rw [comp_whiskerRight, assoc]
    slice_lhs 2 3 => simp
    slice_lhs 3 4 => rw [← whiskerLeft_comp, M.mod.act_assoc]
    simp [whiskerLeft_comp, assoc, -associator_naturality_left,
      -associator_naturality_middle_assoc]

/-- Lemma 2.9.12: For any `X ∈ C`, there is a canonical isomorphism
`Hom_A(X ⊗ A, M) ≃ Hom(X, M)`, expressing the adjunction between `• ⊗ A` and the
forgetful functor from right `A`-modules. -/
noncomputable def Lemma_2_9_12 (X : C) (M : RightMod' A) :
    Hom ⟨X ⊗ A, tensorModObj X (regular A)⟩ M ≃ (X ⟶ M.X) where
  toFun f := (ρ_ X).inv ≫ (X ◁ η[A]) ≫ f.hom
  invFun g := {
    hom := (g ▷ A) ≫ M.mod.act
    comm := by
      simp only [tensorModObj, regular, assoc, comp_whiskerRight]
      rw [M.mod.act_assoc]
      slice_lhs 2 3 => rw [whisker_exchange g μ[A]]
      slice_lhs 1 2 => rw [← associator_naturality_left]
      simp [assoc]
  }
  left_inv f := by
    ext
    simp only [comp_whiskerRight, assoc]
    have hc : f.hom ▷ A ≫ M.mod.act = (α_ X A A).hom ≫ X ◁ μ[A] ≫ f.hom := by
      have := f.comm
      simp only [tensorModObj, regular] at this
      rw [← assoc, ← this]
    rw [hc]
    have h : (ρ_ X).inv ▷ A ≫ (X ◁ η[A]) ▷ A ≫ (α_ X A A).hom ≫ X ◁ μ[A] = 𝟙 (X ⊗ A) := by
      slice_lhs 2 3 => rw [associator_naturality_middle]
      slice_lhs 3 4 => rw [← whiskerLeft_comp, MonObj.one_mul]
      rw [triangle]; simp
    calc (ρ_ X).inv ▷ A ≫ (X ◁ η[A]) ▷ A ≫ (α_ X A A).hom ≫ X ◁ μ[A] ≫ f.hom
        = ((ρ_ X).inv ▷ A ≫ (X ◁ η[A]) ▷ A ≫ (α_ X A A).hom ≫ X ◁ μ[A]) ≫ f.hom := by
          simp [assoc]
      _ = 𝟙 (X ⊗ A) ≫ f.hom := by rw [h]
      _ = f.hom := by simp
  right_inv g := by
    simp only
    rw [whisker_exchange_assoc]
    simp

end RightMod'

/-- The equivalence form of Lemma 2.9.12 with explicit category and monoid arguments. -/
noncomputable def lemma_2_9_12_equiv {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {A : C} [MonObj A] (X : C) (M : RightMod' A) :
    RightMod'.Hom ⟨X ⊗ A, RightMod'.tensorModObj X (RightMod'.regular A)⟩ M ≃ (X ⟶ M.X) :=
  RightMod'.Lemma_2_9_12 X M

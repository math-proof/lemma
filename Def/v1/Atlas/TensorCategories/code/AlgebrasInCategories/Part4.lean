/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/AlgebrasInCategories.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Mon_
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Abbrev.v1.Atlas.TensorCategories.code.ModuleCategory.Part5
import Instance.v1.Atlas.TensorCategories.code.AlgebrasInCategories.Part2
set_option maxHeartbeats 800000

universe v u


namespace CategoryTheory

open Category MonoidalCategory MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

variable (A : C) [MonObj A]

attribute [reassoc (attr := simp)] RightModObj.act_unit RightModObj.act_assoc

variable {A}

attribute [reassoc (attr := simp)] RightMod_.Hom.comm

namespace RightMod_

/-- Proposition 2.9.10: the category `Mod_C(A)` together with the functor `⊗̃` and the
associativity and unit constraints `ã`, `l̃` is a left module category over `C`. -/
def Proposition_2_9_10 : LeftModuleCategory C (RightMod_ (A := A)) :=
  RightMod_.actLeftModuleCategory

/-- Lemma 2.9.12: for any `X ∈ C`, the canonical isomorphism
`Hom_A(X ⊗ A, M) ≃ Hom(X, M)` exhibits `· ⊗ A` as left adjoint to the forgetful functor. -/
noncomputable def Lemma_2_9_12 (X : C) (M : RightMod_ A) :
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

end RightMod_

/-- Two algebras `A` and `B` in `C` are Morita equivalent if there is a module equivalence
between their categories of right modules `RightMod_ A` and `RightMod_ B`. -/
def MoritaEquivalent (A B : C) [MonObj A] [MonObj B] : Prop :=
  Nonempty (ModuleEquivalence C (RightMod_ (C := C) (A := A)) (RightMod_ (C := C) (A := B)))

section TensorOverAlgebra

variable [Limits.HasCoequalizers C]

/-- Tensor product over an algebra `A`: for a right `A`-module `(M, actR)` and a left
`A`-module `(N, actL)`, the object `M ⊗_A N` is the coequalizer of the two natural maps
`M ⊗ A ⊗ N ⇒ M ⊗ N`. -/
noncomputable def TensorOverAlgebra {A M N : C}
    (actR : M ⊗ A ⟶ M) (actL : A ⊗ N ⟶ N) : C :=
  Limits.coequalizer
    ((α_ M A N).inv ≫ (actR ▷ N))
    (M ◁ actL)

/-- The canonical projection `M ⊗ N ⟶ M ⊗_A N` exhibiting `M ⊗_A N` as the coequalizer. -/
noncomputable def TensorOverAlgebra.π {A M N : C}
    (actR : M ⊗ A ⟶ M) (actL : A ⊗ N ⟶ N) :
    M ⊗ N ⟶ TensorOverAlgebra actR actL :=
  Limits.coequalizer.π _ _

end TensorOverAlgebra
end CategoryTheory

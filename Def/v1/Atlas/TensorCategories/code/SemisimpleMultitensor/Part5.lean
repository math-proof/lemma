/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SemisimpleMultitensor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Structure.v1.Atlas.TensorCategories.code.PivotalSpherical.Part3
import Lemma.Category.Atlas.v1.TensorCategories.code.PivotalSpherical
import Theorem.v1.Atlas.TensorCategories.code.SemisimpleMultitensor.Part4
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory CategoryTheory.Limits

universe v u


noncomputable section

namespace CategoryTheory

section UnitSemisimple

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasZeroMorphisms C]

section ComponentSubcategories

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasZeroMorphisms C]

section RigidDuals

variable [RigidCategory C]

/-- Each simple summand `f i` of a decomposition of the unit is canonically isomorphic to its own
right dual, via the mates of the structural inclusion and projection maps. -/
def unitComponent_selfDual {n : ℕ} (f : Fin n → C) [HasBiproduct f]
    (hiso : 𝟙_ C ≅ ⨁ f) (hsimp : ∀ i, Simple (f i))
    (i : Fin n) :
    f i ≅ (f i)ᘁ := by
  set s : f i ⟶ 𝟙_ C := biproduct.ι f i ≫ hiso.inv
  set r : 𝟙_ C ⟶ f i := hiso.hom ≫ biproduct.π f i
  have h_sr : s ≫ r = 𝟙 (f i) := by
    simp [s, r, Category.assoc, Iso.inv_hom_id_assoc]
  have h_rs_mate_eq : rightAdjointMate s ≫ rightAdjointMate r = r ≫ s := by
    rw [← comp_rightAdjointMate]
    exact rightAdjointMate_unit_endo (r ≫ s)
  have h_rs_mate_id : rightAdjointMate r ≫ rightAdjointMate s = 𝟙 (f i)ᘁ := by
    rw [← comp_rightAdjointMate, h_sr, rightAdjointMate_id]
  refine ⟨s ≫ rightAdjointMate s, rightAdjointMate r ≫ r, ?_, ?_⟩
  ·
    simp only [Category.assoc]
    slice_lhs 3 4 => rw [h_rs_mate_eq]
    simp only [Category.assoc, r, s, Iso.inv_hom_id_assoc, biproduct.ι_π_self, Category.comp_id]
  ·
    rw [Category.assoc, ← Category.assoc r s _, h_rs_mate_eq.symm, Category.assoc,
        ← Category.assoc (rightAdjointMate r) (rightAdjointMate s) _, h_rs_mate_id, Category.id_comp]

/-- The right dual of a tensor product is canonically isomorphic to the reversed tensor product of
right duals, `(A ⊗ B)ᘁ ≅ Bᘁ ⊗ Aᘁ`, constructed via uniqueness of right adjoints. -/
def rightDualTensorIso (A B : C) : (A ⊗ B)ᘁ ≅ (Bᘁ : C) ⊗ (Aᘁ : C) := by
  have adj1 := tensorRightAdjunction (A ⊗ B) ((A ⊗ B)ᘁ)
  have comp_adj := (tensorRightAdjunction A (Aᘁ : C)).comp (tensorRightAdjunction B (Bᘁ : C))
  have assoc1 : tensorRight A ⋙ tensorRight B ≅ tensorRight (A ⊗ B) :=
    NatIso.ofComponents (fun X => (α_ X A B)) (by intros; simp [tensorRight])
  have assoc2 : tensorRight (Bᘁ : C) ⋙ tensorRight (Aᘁ : C) ≅
      tensorRight ((Bᘁ : C) ⊗ (Aᘁ : C)) :=
    NatIso.ofComponents (fun X => (α_ X Bᘁ Aᘁ)) (by intros; simp [tensorRight])
  have adj2 := (comp_adj.ofNatIsoLeft assoc1).ofNatIsoRight assoc2
  exact (λ_ ((A ⊗ B)ᘁ)).symm ≪≫
    (Adjunction.rightAdjointUniq adj1 adj2).app (𝟙_ C) ≪≫
    (λ_ ((Bᘁ : C) ⊗ (Aᘁ : C)))

/-- The left dual of a tensor product is canonically isomorphic to the reversed tensor product of
left duals, `ᘁ(A ⊗ B) ≅ ᘁB ⊗ ᘁA`, constructed via uniqueness of right adjoints. -/
def leftDualTensorIso (A B : C) : (ᘁ(A ⊗ B) : C) ≅ (ᘁB : C) ⊗ (ᘁA : C) := by
  have adj1 := tensorLeftAdjunction (ᘁ(A ⊗ B) : C) (A ⊗ B)
  have comp_adj := (tensorLeftAdjunction (ᘁB : C) B).comp
    (tensorLeftAdjunction (ᘁA : C) A)
  have assoc1 : tensorLeft B ⋙ tensorLeft A ≅ tensorLeft (A ⊗ B) :=
    NatIso.ofComponents (fun Z => (α_ A B Z).symm) (by intros; simp [tensorLeft])
  have assoc2 : tensorLeft (ᘁA : C) ⋙ tensorLeft (ᘁB : C) ≅
      tensorLeft ((ᘁB : C) ⊗ (ᘁA : C)) :=
    NatIso.ofComponents (fun Z => (α_ (ᘁB : C) (ᘁA : C) Z).symm)
      (by intros; simp [tensorLeft])
  have adj2 := (comp_adj.ofNatIsoLeft assoc1).ofNatIsoRight assoc2
  exact (ρ_ (ᘁ(A ⊗ B) : C)).symm ≪≫
    (Adjunction.rightAdjointUniq adj1 adj2).app (𝟙_ C) ≪≫
    (ρ_ ((ᘁB : C) ⊗ (ᘁA : C)))

/-- Given a self-duality isomorphism `V ≅ Vᘁ`, transport it through left adjoint mates to
produce an isomorphism `ᘁV ≅ V`. -/
def leftDualSelfDual {V : C} (selfDual : V ≅ Vᘁ) : (ᘁV : C) ≅ V where
  hom := ᘁ(selfDual.inv)
  inv := ᘁ(selfDual.hom)
  hom_inv_id := by rw [← comp_leftAdjointMate]; simp
  inv_hom_id := by rw [← comp_leftAdjointMate]; simp

/-- The right dual of an `(i, j)`-component object `f i ⊗ X ⊗ f j` is identified with the
`(j, i)`-component object on the dual `Xᘁ`, swapping the indices. -/
def rightDual_component {n : ℕ} (f : Fin n → C) [HasBiproduct f]
    (hiso : 𝟙_ C ≅ ⨁ f) (hsimp : ∀ i, Simple (f i))
    (X : C) (i j : Fin n) :
    (componentObj f X i j)ᘁ ≅ componentObj f (Xᘁ) j i := by
  unfold componentObj
  exact rightDualTensorIso (f i) (X ⊗ f j) ≪≫
    tensorIso (rightDualTensorIso X (f j)) (Iso.refl _) ≪≫
    (α_ (f j)ᘁ (Xᘁ : C) (f i)ᘁ) ≪≫
    tensorIso (unitComponent_selfDual f hiso hsimp j).symm
              (tensorIso (Iso.refl (Xᘁ : C)) (unitComponent_selfDual f hiso hsimp i).symm)

/-- The left dual of an `(i, j)`-component object `f i ⊗ X ⊗ f j` is identified with the
`(j, i)`-component object on the left dual `ᘁX`, swapping the indices. -/
def leftDual_component {n : ℕ} (f : Fin n → C) [HasBiproduct f]
    (hiso : 𝟙_ C ≅ ⨁ f) (hsimp : ∀ i, Simple (f i))
    (X : C) (i j : Fin n) :
    (ᘁ(componentObj f X i j) : C) ≅ componentObj f (ᘁX : C) j i := by
  unfold componentObj
  exact leftDualTensorIso (f i) (X ⊗ f j) ≪≫
    tensorIso (leftDualTensorIso X (f j)) (Iso.refl _) ≪≫
    (α_ (ᘁ(f j) : C) (ᘁX : C) (ᘁ(f i) : C)) ≪≫
    tensorIso (leftDualSelfDual (unitComponent_selfDual f hiso hsimp j))
              (tensorIso (Iso.refl (ᘁX : C)) (leftDualSelfDual (unitComponent_selfDual f hiso hsimp i)))

end RigidDuals

end ComponentSubcategories

section ObjectDecomposition

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [Preadditive C] [MonoidalPreadditive C] [HasFiniteBiproducts C]

/-- Canonical isomorphism flattening a double biproduct over `Fin n × Fin n` into a single biproduct
indexed by the product type. -/
def biproductFlattenIso {n : ℕ} (g : Fin n → Fin n → C) :
    (⨁ fun i => ⨁ fun j => g i j) ≅ (⨁ fun p : Fin n × Fin n => g p.1 p.2) where
  hom := biproduct.desc fun i => biproduct.desc fun j =>
    biproduct.ι (fun p : Fin n × Fin n => g p.1 p.2) ⟨i, j⟩
  inv := biproduct.desc fun (p : Fin n × Fin n) =>
    biproduct.ι (fun j => g p.1 j) p.2 ≫ biproduct.ι (fun i => ⨁ fun j => g i j) p.1
  hom_inv_id := by ext i j; simp
  inv_hom_id := by ext ⟨i, j⟩; simp

end ObjectDecomposition
end UnitSemisimple
end CategoryTheory
end

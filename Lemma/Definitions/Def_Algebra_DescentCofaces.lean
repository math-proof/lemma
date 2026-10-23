import Mathlib

set_option autoImplicit false

universe u

open TensorProduct CategoryTheory

noncomputable section

namespace Algebra.DescentCofaces

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

abbrev R₂ : CommRingCat.{u} := CommRingCat.of (B ⊗[A] B)

abbrev R₃ : CommRingCat.{u} := CommRingCat.of (B ⊗[A] (B ⊗[A] B))

def i₁ : CommRingCat.of B ⟶ R₂ A B := CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom

def i₂ : CommRingCat.of B ⟶ R₂ A B :=
  CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := B)).toRingHom

def c₁₂ : R₂ A B ⟶ R₃ A B :=
  CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A B)
    (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := B) (B := B))).toRingHom

def c₂₃ : R₂ A B ⟶ R₃ A B :=
  CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := B ⊗[A] B)).toRingHom

def c₁₃ : R₂ A B ⟶ R₃ A B :=
  CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A B)
    (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := B))).toRingHom

@[simp] theorem i₁_apply (b : B) : (i₁ A B).hom b = b ⊗ₜ 1 := rfl
@[simp] theorem i₂_apply (b : B) : (i₂ A B).hom b = 1 ⊗ₜ b := rfl
@[simp] theorem c₁₂_tmul (b b' : B) : (c₁₂ A B).hom (b ⊗ₜ b') = b ⊗ₜ (b' ⊗ₜ 1) := rfl
@[simp] theorem c₂₃_tmul (b b' : B) : (c₂₃ A B).hom (b ⊗ₜ b') = 1 ⊗ₜ (b ⊗ₜ b') := rfl
@[simp] theorem c₁₃_tmul (b b' : B) : (c₁₃ A B).hom (b ⊗ₜ b') = b ⊗ₜ (1 ⊗ₜ b') := rfl

theorem i₁_c₁₂ : i₁ A B ≫ c₁₂ A B = i₁ A B ≫ c₁₃ A B := rfl
theorem i₂_c₁₂ : i₂ A B ≫ c₁₂ A B = i₁ A B ≫ c₂₃ A B := rfl
theorem i₂_c₁₃ : i₂ A B ≫ c₁₃ A B = i₂ A B ≫ c₂₃ A B := rfl

theorem algebraMap_i₁_eq_i₂ :
    CommRingCat.ofHom (algebraMap A B) ≫ i₁ A B = CommRingCat.ofHom (algebraMap A B) ≫ i₂ A B := by
  ext a
  change algebraMap A B a ⊗ₜ[A] (1 : B) = (1 : B) ⊗ₜ[A] algebraMap A B a
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem i₁_comp_algebraMap_eq :
    (i₁ A B).hom.comp (algebraMap A B) = (i₂ A B).hom.comp (algebraMap A B) :=
  congrArg CommRingCat.Hom.hom (algebraMap_i₁_eq_i₂ A B)

def canonical (M : ModuleCat.{u} A) :
    (ModuleCat.extendScalars (i₁ A B).hom).obj ((ModuleCat.extendScalars (algebraMap A B)).obj M) ⟶
      (ModuleCat.extendScalars (i₂ A B).hom).obj ((ModuleCat.extendScalars (algebraMap A B)).obj M) :=
  (ModuleCat.extendScalarsComp (algebraMap A B) (i₁ A B).hom).inv.app M ≫
    eqToHom (congrArg (fun f : A →+* B ⊗[A] B => (ModuleCat.extendScalars f).obj M)
      (i₁_comp_algebraMap_eq A B)) ≫
    (ModuleCat.extendScalarsComp (algebraMap A B) (i₂ A B).hom).hom.app M

variable {A B} in

def T (N : ModuleCat.{u} B) (c : R₂ A B ⟶ R₃ A B)
    (φ' : (ModuleCat.extendScalars (i₁ A B).hom).obj N ⟶ (ModuleCat.extendScalars (i₂ A B).hom).obj N) :
    (ModuleCat.extendScalars (i₁ A B ≫ c).hom).obj N ⟶ (ModuleCat.extendScalars (i₂ A B ≫ c).hom).obj N :=
  (ModuleCat.extendScalarsComp (i₁ A B).hom c.hom).hom.app N ≫
    (ModuleCat.extendScalars c.hom).map φ' ≫
    (ModuleCat.extendScalarsComp (i₂ A B).hom c.hom).inv.app N

variable {A B} in

def Cocycle (N : ModuleCat.{u} B)
    (φ' : (ModuleCat.extendScalars (i₁ A B).hom).obj N ⟶ (ModuleCat.extendScalars (i₂ A B).hom).obj N) : Prop :=
  T N (c₁₂ A B) φ' ≫ T N (c₂₃ A B) φ' = T N (c₁₃ A B) φ'

end Algebra.DescentCofaces

end

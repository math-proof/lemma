import Mathlib

set_option autoImplicit false

open LinearMap Submodule Function

universe u v

namespace Deformation

variable {𝓞 : Type u} [CommRing 𝓞]

@[ext]
structure DieudonneDatum (ℓ : 𝓞) (D : Type v) [AddCommGroup D] [Module 𝓞 D] where

  F : D →ₗ[𝓞] D

  V : D →ₗ[𝓞] D

  fv : F ∘ₗ V = ℓ • LinearMap.id

  vf : V ∘ₗ F = ℓ • LinearMap.id

namespace DieudonneDatum

variable {ℓ : 𝓞} {D : Type v} [AddCommGroup D] [Module 𝓞 D] (M : DieudonneDatum ℓ D)

theorem F_V_apply (x : D) : M.F (M.V x) = ℓ • x := by
  have := LinearMap.congr_fun M.fv x; simpa using this

theorem V_F_apply (x : D) : M.V (M.F x) = ℓ • x := by
  have := LinearMap.congr_fun M.vf x; simpa using this

theorem F_V_comm : M.F ∘ₗ M.V = M.V ∘ₗ M.F := M.fv.trans M.vf.symm

def IsEtaleType : Prop := Function.Bijective M.F

def IsMultiplicativeType : Prop := Function.Bijective M.V

def IsLocalLocal : Prop := M.F = 0 ∧ M.V = 0

theorem V_eq_smul_of_isEtaleType (h : M.IsEtaleType) (x : D) :
    M.V x = ℓ • (Equiv.ofBijective M.F h).symm x := by
  apply h.injective
  rw [M.F_V_apply, map_smul]
  congr 1
  exact ((Equiv.ofBijective M.F h).apply_symm_apply x).symm

variable (ℓ) in

def etaleOne : DieudonneDatum ℓ 𝓞 where
  F := LinearMap.id
  V := ℓ • LinearMap.id
  fv := by ext; simp
  vf := by ext; simp

variable (ℓ) in

def multOne : DieudonneDatum ℓ 𝓞 where
  F := ℓ • LinearMap.id
  V := LinearMap.id
  fv := by ext; simp
  vf := by ext; simp

theorem etaleOne_isEtaleType : (etaleOne (𝓞 := 𝓞) ℓ).IsEtaleType :=
  Function.bijective_id

theorem multOne_isMultiplicativeType : (multOne (𝓞 := 𝓞) ℓ).IsMultiplicativeType :=
  Function.bijective_id

end DieudonneDatum

structure HondaSystem (ℓ : 𝓞) (D : Type v) [AddCommGroup D] [Module 𝓞 D] extends
    DieudonneDatum ℓ D where

  L : Submodule 𝓞 D

  sh1_le : ∀ x ∈ L, x ∈ LinearMap.range F → ∃ y ∈ L, x = ℓ • y

  sh1_ge : ∀ y ∈ L, ℓ • y ∈ LinearMap.range F

  sh2' : (LinearMap.range F) ⊔ L = ⊤

  sh3 : ∀ x ∈ L, V x = 0 → x = 0

end Deformation

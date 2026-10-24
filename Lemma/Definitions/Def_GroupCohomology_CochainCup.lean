import Mathlib

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

namespace groupCohomology

variable {k G : Type u} [CommRing k] [Group G] (A B : Rep.{u} k G) (p q : ℕ)

abbrev cochainCupFst (σ : Fin (p + q) → G) : Fin p → G := fun i => σ (Fin.castAdd q i)

abbrev cochainCupSnd (σ : Fin (p + q) → G) : Fin q → G := fun j => σ (Fin.natAdd p j)

noncomputable def cochainCup :
    ((Fin p → G) → A) →ₗ[k] ((Fin q → G) → B) →ₗ[k] ((Fin (p + q) → G) → (A ⊗ B : Rep k G)) :=
  LinearMap.mk₂ k
    (fun f g σ => f (cochainCupFst p q σ) ⊗ₜ[k] B.ρ (Fin.partialProd (cochainCupFst p q σ) (Fin.last p)) (g (cochainCupSnd p q σ)))
    (fun f₁ f₂ g => funext fun σ => by simp only [Pi.add_apply, TensorProduct.add_tmul])
    (fun c f g => funext fun σ => by simp only [Pi.smul_apply, TensorProduct.smul_tmul'])
    (fun f g₁ g₂ => funext fun σ => by simp only [Pi.add_apply, map_add, TensorProduct.tmul_add])
    (fun c f g => funext fun σ => by simp only [Pi.smul_apply, map_smul, TensorProduct.tmul_smul])

theorem cochainCup_apply (f : (Fin p → G) → A) (g : (Fin q → G) → B) (σ : Fin (p + q) → G) :
    cochainCup A B p q f g σ
      = f (cochainCupFst p q σ) ⊗ₜ[k] B.ρ (Fin.partialProd (cochainCupFst p q σ) (Fin.last p)) (g (cochainCupSnd p q σ)) := rfl

end groupCohomology

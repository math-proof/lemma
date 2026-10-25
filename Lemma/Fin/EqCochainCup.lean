import Mathlib
import sympy.Basic
open CategoryTheory MonoidalCategory
set_option autoImplicit false


universe u


variable {k G : Type u} [CommRing k] [Group G] (A B : Rep.{u} k G) (p q : ℕ)

abbrev CochainCupFst (σ : Fin (p + q) → G) : Fin p → G := fun i => σ (Fin.castAdd q i)

abbrev CochainCupSnd (σ : Fin (p + q) → G) : Fin q → G := fun j => σ (Fin.natAdd p j)

noncomputable def CochainCup :
  ((Fin p → G) → A) →ₗ[k] ((Fin q → G) → B) →ₗ[k] ((Fin (p + q) → G) → (A ⊗ B : Rep k G)) :=
  LinearMap.mk₂ k
    (fun f g σ => f (CochainCupFst p q σ) ⊗ₜ[k] B.ρ (Fin.partialProd (CochainCupFst p q σ) (Fin.last p)) (g (CochainCupSnd p q σ)))
    (fun f₁ f₂ g => funext fun σ => by simp only [Pi.add_apply, TensorProduct.add_tmul])
    (fun c f g => funext fun σ => by simp only [Pi.smul_apply, TensorProduct.smul_tmul'])
    (fun f g₁ g₂ => funext fun σ => by simp only [Pi.add_apply, map_add, TensorProduct.tmul_add])
    (fun c f g => funext fun σ => by simp only [Pi.smul_apply, map_smul, TensorProduct.tmul_smul])


/--
[cochainCup_apply]
-/
@[path]
private lemma main
-- given
  (f : (Fin p → G) → A) (g : (Fin q → G) → B) (σ : Fin (p + q) → G) :
-- imply
  CochainCup A B p q f g σ =
    f (CochainCupFst p q σ) ⊗ₜ[k] B.ρ (Fin.partialProd (CochainCupFst p q σ) (Fin.last p)) (g (CochainCupSnd p q σ)) := by
-- proof
  rfl


-- created on 2026-10-24

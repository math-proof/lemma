import Mathlib
import sympy.Basic
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[Bialgebra_bialgEquiv_comp_eq_tensorProduct_map_comp_of_productMap](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Bialgebra_bialgEquiv_comp_eq_tensorProduct_map_comp_of_productMap.lean)
-/
@[path]
private lemma main
  (k : Type u) [Field k]
  {A : Type u} [CommRing A] [Bialgebra k A]
  {C : Type u} [CommRing C] [Bialgebra k C]
  {A' : Type u} [CommRing A'] [Bialgebra k A']
  {C' : Type u} [CommRing C'] [Bialgebra k C']
  (ρ₀ ρ₁ : BialgHom k A C) (ρ₀' ρ₁' : BialgHom k A' C')
  (κ : BialgEquiv k C (A ⊗[k] A)) (κ' : BialgEquiv k C' (A' ⊗[k] A'))
  (hκ : ∀ x : A ⊗[k] A, κ.symm x = Algebra.TensorProduct.productMap (ρ₀ : AlgHom k A C) (ρ₁ : AlgHom k A C) x)
  (hκ' : ∀ x : A' ⊗[k] A', κ'.symm x = Algebra.TensorProduct.productMap (ρ₀' : AlgHom k A' C') (ρ₁' : AlgHom k A' C') x)
  (tA : BialgHom k A' A) (tC : BialgHom k C' C)
  (h₀ : ∀ a : A', tC (ρ₀' a) = ρ₀ (tA a)) (h₁ : ∀ a : A', tC (ρ₁' a) = ρ₁ (tA a)) :
  -- imply
  (κ : BialgHom k C (A ⊗[k] A)).comp tC = (Bialgebra.TensorProduct.map tA tA).comp (κ' : BialgHom k C' (A' ⊗[k] A')) := by
  -- proof
  have key : ∀ z : A' ⊗[k] A', κ.symm (Bialgebra.TensorProduct.map tA tA z) = tC (κ'.symm z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      rw [Bialgebra.TensorProduct.map_tmul, hκ, hκ', Algebra.TensorProduct.productMap_apply_tmul, Algebra.TensorProduct.productMap_apply_tmul, map_mul]
      change ρ₀ (tA a) * ρ₁ (tA b) = tC (ρ₀' a) * tC (ρ₁' b)
      rw [← h₀, ← h₁]
    | add x y hx hy => rw [map_add, map_add, hx, hy, ← map_add, ← map_add]
  apply BialgHom.coe_toAlgHom_injective
  apply AlgHom.ext
  intro y
  obtain ⟨z, rfl⟩ := κ'.symm.surjective y
  change κ (tC (κ'.symm z)) = Bialgebra.TensorProduct.map tA tA (κ' (κ'.symm z))
  rw [← key, BialgEquiv.apply_symm_apply, BialgEquiv.apply_symm_apply]


-- created on 2026-10-20

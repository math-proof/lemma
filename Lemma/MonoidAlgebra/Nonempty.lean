import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/--
[Bialgebra_nonempty_bialgEquiv_monoidAlgebra_of_basis_pow_of_comul_eq_tmul_self](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Bialgebra_nonempty_bialgEquiv_monoidAlgebra_of_basis_pow_of_comul_eq_tmul_self.lean)
-/
@[path]
private lemma main
    {R : Type u} [CommRing R] {H : Type v} [CommRing H] [Bialgebra R H]
    (n : ℕ) [NeZero n] (x : H)
    (hΔ : Coalgebra.comul (R := R) x = x ⊗ₜ[R] x) (hε : Coalgebra.counit (R := R) x = 1)
    (hxn : x ^ n = 1)
    (b : Module.Basis (Fin n) R H) (hb : ∀ i : Fin n, b i = x ^ (i : ℕ)) :
    Nonempty (H ≃ₐc[R] MonoidAlgebra R (Multiplicative (ZMod n))) := by
  classical
  have hmod : ∀ m : ℕ, x ^ (m % n) = x ^ m := fun m => by
    conv_rhs => rw [← Nat.mod_add_div m n, pow_add, pow_mul, hxn, one_pow, mul_one]
  let φ : Multiplicative (ZMod n) →* H :=
    { toFun := fun g => x ^ (Multiplicative.toAdd g).val
      map_one' := by simp
      map_mul' := fun g h => by
        simp only [toAdd_mul]
        rw [ZMod.val_add, hmod, pow_add] }
  have hφ : ∀ g, φ g = x ^ (Multiplicative.toAdd g).val := fun g => rfl
  let e : Multiplicative (ZMod n) ≃ Fin n :=
    { toFun := fun g => ⟨(Multiplicative.toAdd g).val, ZMod.val_lt _⟩
      invFun := fun i => Multiplicative.ofAdd ((i : ℕ) : ZMod n)
      left_inv := fun g => by simp
      right_inv := fun i => by ext; simp [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt] }
  have he : ∀ g, ((e g : Fin n) : ℕ) = (Multiplicative.toAdd g).val := fun g => rfl
  let θ : MonoidAlgebra R (Multiplicative (ZMod n)) →ₐ[R] H := MonoidAlgebra.lift R H _ φ
  have hθ1 : ∀ g, θ (MonoidAlgebra.single g 1) = x ^ (Multiplicative.toAdd g).val := by
    intro g
    rw [MonoidAlgebra.lift_single, one_smul, hφ]
  let b' : Module.Basis (Multiplicative (ZMod n)) R H := b.reindex e.symm
  have hb' : ∀ g, b' g = x ^ (Multiplicative.toAdd g).val := by
    intro g
    rw [Module.Basis.reindex_apply, Equiv.symm_symm, hb, he]
  have hlin : θ.toLinearMap = (b'.repr.symm : (Multiplicative (ZMod n) →₀ R) →ₗ[R] H) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv R).toLinearMap := by
    apply MonoidAlgebra.lhom_ext'
    intro g
    apply LinearMap.ext_ring
    simp only [LinearMap.comp_apply, MonoidAlgebra.lsingle_apply, LinearEquiv.coe_coe,
      MonoidAlgebra.coeffLinearEquiv_apply, MonoidAlgebra.coeff_single,
      Module.Basis.repr_symm_apply, Finsupp.linearCombination_single, one_smul, hb']
    exact hθ1 g
  have hbij : Function.Bijective θ := by
    have hcoe : ⇑θ = ⇑(b'.repr.symm) ∘ ⇑(MonoidAlgebra.coeffLinearEquiv R (S := R)
        (M := Multiplicative (ZMod n))) := congrArg DFunLike.coe hlin
    rw [hcoe]
    exact b'.repr.symm.bijective.comp (MonoidAlgebra.coeffLinearEquiv R).bijective
  let f : MonoidAlgebra R (Multiplicative (ZMod n)) ≃ₐ[R] H := AlgEquiv.ofBijective θ hbij
  have hf : ∀ a, f a = θ a := fun a => rfl
  have hΔk : ∀ k : ℕ, Coalgebra.comul (R := R) (x ^ k) = (x ^ k) ⊗ₜ[R] (x ^ k) := by
    intro k
    rw [← Bialgebra.comulAlgHom_apply, map_pow, Bialgebra.comulAlgHom_apply, hΔ, Algebra.TensorProduct.tmul_pow]
  have hεk : ∀ k : ℕ, Coalgebra.counit (R := R) (x ^ k) = 1 := by
    intro k
    rw [← Bialgebra.counitAlgHom_apply, map_pow, Bialgebra.counitAlgHom_apply, hε, one_pow]
  refine ⟨(BialgEquiv.ofAlgEquiv f ?_ ?_).symm⟩
  · apply MonoidAlgebra.algHom_ext _ (Subsingleton.elim _ _)
    intro g
    simp [hf, hθ1, hεk]
  · apply MonoidAlgebra.algHom_ext _ (Subsingleton.elim _ _)
    intro g
    simp [hf, hθ1, hΔk, CommSemiring.comul_apply]

-- created on 2026-10-20

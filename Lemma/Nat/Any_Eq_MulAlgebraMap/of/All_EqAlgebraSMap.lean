import Mathlib
import sympy.Basic

open scoped TensorProduct

/--
[FullLevelTate_exists_linearEquiv_cancelBaseChange_of_algebraMap_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_FullLevelTate_exists_linearEquiv_cancelBaseChange_of_algebraMap_eq.lean)
-/
@[main]
private lemma main
  [CommRing O'] [CommRing K] [Algebra O' K] [AddCommMonoid T]
  {lam : ℕ} [Fact lam.Prime] [Algebra ℤ_[lam] O'] [Algebra ℚ_[lam] K] [Module ℤ_[lam] T]
-- given
  (hOK : ∀ z : ℤ_[lam], algebraMap O' K (algebraMap ℤ_[lam] O' z) = algebraMap ℚ_[lam] K (z : ℚ_[lam])) :
-- imply
  ∃ e : K ⊗[O'] (O' ⊗[ℤ_[lam]] T) ≃ₗ[K] K ⊗[ℚ_[lam]] (ℚ_[lam] ⊗[ℤ_[lam]] T),
      ∀ (c : K) (a : O') (x : T),
        e (c ⊗ₜ[O'] (a ⊗ₜ[ℤ_[lam]] x)) = (algebraMap O' K a * c) ⊗ₜ[ℚ_[lam]] ((1 : ℚ_[lam]) ⊗ₜ[ℤ_[lam]] x) := by
-- proof
  classical
  let : Algebra ℤ_[lam] K := ((algebraMap O' K).comp (algebraMap ℤ_[lam] O')).toAlgebra
  have hT1 : IsScalarTower ℤ_[lam] O' K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hT2 : IsScalarTower ℤ_[lam] ℚ_[lam] K := by
    refine IsScalarTower.of_algebraMap_eq (fun z => ?_)
    show algebraMap O' K (algebraMap ℤ_[lam] O' z) = _
    rw [hOK z]
    rfl
  let e₁ : K ⊗[O'] (O' ⊗[ℤ_[lam]] T) ≃ₗ[K] K ⊗[ℤ_[lam]] T :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ_[lam] O' K K T
  let e₂ : K ⊗[ℚ_[lam]] (ℚ_[lam] ⊗[ℤ_[lam]] T) ≃ₗ[K] K ⊗[ℤ_[lam]] T :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ_[lam] ℚ_[lam] K K T
  refine ⟨e₁.trans e₂.symm, fun c a x => ?_⟩
  rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_eq]
  simp only [e₁, e₂, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, Algebra.smul_def, map_one,
    one_mul]


-- created on 2026-10-05

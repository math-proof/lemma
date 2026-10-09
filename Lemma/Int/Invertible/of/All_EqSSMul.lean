import Mathlib
import sympy.Basic


/--
[Module_Invertible_of_ringEquiv](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_Invertible_of_ringEquiv.lean)
-/
@[path]
private lemma main
  {R R' : Type u} [CommRing R] [CommRing R']
  {M : Type v} [AddCommGroup M] [Module R' M] [Module.Invertible R' M] [Module R M]
-- given
  (σ : R ≃+* R')
  (hσ : ∀ (r : R) (m : M), r • m = σ r • m) :
-- imply
  Module.Invertible R M := by
-- proof
  let : Algebra R' R := σ.symm.toRingHom.toAlgebra
  have : IsScalarTower R' R M := ⟨fun r' r m => by
    rw [Algebra.smul_def, hσ, hσ r m, ← mul_smul]
    congr 1
    simp [RingHom.algebraMap_toAlgebra]⟩
  have : IsLocalization (⊥ : Submonoid R') R :=
    IsLocalization.of_le_isUnit_of_bijective
      (by
        rintro _ ⟨x, hx, rfl⟩
        have hx1 : x = 1 := by simpa using hx
        subst hx1
        simp)
      σ.symm.bijective
  have : IsLocalizedModule (⊥ : Submonoid R') (LinearMap.id : M →ₗ[R'] M) :=
    isLocalizedModule_id (S := (⊥ : Submonoid R')) (M := M) (R' := R)
  exact Module.Invertible.of_isLocalization (⊥ : Submonoid R') (LinearMap.id : M →ₗ[R'] M)


-- created on 2026-10-05

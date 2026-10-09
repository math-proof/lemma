import Mathlib
import sympy.Basic


/--
[MonoidHom_charpoly_apply_mul_mul_inv](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_MonoidHom_charpoly_apply_mul_mul_inv.lean)
-/
@[path]
private lemma main
  [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] [Group G]
  {ρ : G →* Module.End R M}
  {σ τ : G} :
-- imply
  (ρ (τ * σ * τ⁻¹)).charpoly = (ρ σ).charpoly := by
-- proof
  let e : M ≃ₗ[R] M := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.toHomUnits τ)
  have he : e.conj (ρ σ) = ρ (τ * σ * τ⁻¹) := by
    rw [map_mul, map_mul]
    rfl
  rw [← he, LinearEquiv.charpoly_conj]


-- created on 2026-10-03

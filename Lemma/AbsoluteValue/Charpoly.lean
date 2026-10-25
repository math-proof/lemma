import Mathlib
import sympy.Basic
import Def.GaloisRep_Adic
import Lemma.Int.P2MUtil


/--
[GaloisRepAdic_charpoly_eq_of_isEquiv](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_GaloisRepAdic_charpoly_eq_of_isEquiv.lean)
-/
@[path]
private lemma main
  [CommRing A] [IsLocalRing A]
  {ρ₁ ρ₂ : GaloisRepAdic A}
-- given
  (h : ρ₁.IsEquiv ρ₂)
  (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
-- imply
  LinearMap.charpoly (ρ₁.ρ σ) = LinearMap.charpoly (ρ₂.ρ σ) := by
-- proof
  obtain ⟨e⟩ := h
  have hconj : ρ₂.ρ σ = (e.toLinearEquiv : ρ₁.V →ₗ[A] ρ₂.V) ∘ₗ ρ₁.ρ σ ∘ₗ
      (e.toLinearEquiv.symm : ρ₂.V →ₗ[A] ρ₁.V) := by
    refine LinearMap.ext fun y => ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, e.map_apply,
      LinearEquiv.apply_symm_apply]
  rw [hconj]
  exact (LinearEquiv.charpoly_conj e.toLinearEquiv (ρ₁.ρ σ)).symm


-- created on 2026-10-23

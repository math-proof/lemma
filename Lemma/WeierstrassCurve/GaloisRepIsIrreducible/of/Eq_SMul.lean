import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.FLTPrelim.GaloisRep
import Lemma.Int.P2MUtil
open Int
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point


/--
[WeierstrassCurve_Affine_Point_galoisRepIsIrreducible_iff_of_linearEquiv](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_Point_galoisRepIsIrreducible_iff_of_linearEquiv.lean)
-/
@[path]
private lemma main
  [Field F] [Field K] [Algebra F K] [DecidableEq K]
  {E₁ E₂ : WeierstrassCurve F}
  {n : ℕ}
-- given
  (φ : Submodule.torsionBy ℤ (E₁⁄K).Point n ≃ₗ[ZMod n] Submodule.torsionBy ℤ (E₂⁄K).Point n)
  (hφ : ∀ (σ : K ≃ₐ[F] K) (x : Submodule.torsionBy ℤ (E₁⁄K).Point n), φ (σ • x) = σ • φ x) :
-- imply
  GaloisRepIsIrreducible (K := K) F E₁ n ↔ GaloisRepIsIrreducible (K := K) F E₂ n := by
-- proof
  constructor
  · intro h
    obtain ⟨hnt, hirr⟩ := h
    refine ⟨φ.injective.nontrivial, fun N hN => ?_⟩
    have hst : IsGaloisStable F (N.comap φ.toLinearMap) := fun σ x hx => by
      simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at hx ⊢
      rw [hφ]
      exact hN σ _ hx
    rw [← Submodule.map_comap_eq_of_surjective φ.surjective N]
    obtain hbot | htop := hirr _ hst
    ·
      left
      rw [hbot, Submodule.map_bot]
    ·
      right
      rw [htop, Submodule.map_top]
      exact LinearMap.range_eq_top.mpr φ.surjective
  · intro h
    have hφ' : ∀ (σ : K ≃ₐ[F] K) (y : Submodule.torsionBy ℤ (E₂⁄K).Point n),
        φ.symm (σ • y) = σ • φ.symm y := by
      intro σ y
      apply φ.injective
      rw [LinearEquiv.apply_symm_apply, hφ, LinearEquiv.apply_symm_apply]
    obtain ⟨hnt, hirr⟩ := h
    refine ⟨φ.symm.injective.nontrivial, fun N hN => ?_⟩
    have hst : IsGaloisStable F (N.comap φ.symm.toLinearMap) := fun σ x hx => by
      simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at hx ⊢
      rw [hφ']
      exact hN σ _ hx
    rw [← Submodule.map_comap_eq_of_surjective φ.symm.surjective N]
    obtain hbot | htop := hirr _ hst
    ·
      left
      rw [hbot, Submodule.map_bot]
    ·
      right
      rw [htop, Submodule.map_top]
      exact LinearMap.range_eq_top.mpr φ.symm.surjective


-- created on 2026-10-24

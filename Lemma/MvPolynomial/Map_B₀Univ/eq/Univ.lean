import Mathlib
import sympy.Basic
import Lemma.ModularCurve.LevelModuliPackage
import Lemma.ModularCurve.LevelModuliPackageAbs
import Lemma.Int.P2MUtil

open ModularCurve

/--
[ModularCurve_LevelModuliPackageAbs_exists_algEquiv_map_univ_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_LevelModuliPackageAbs_exists_algEquiv_map_univ_eq.lean)
-/
@[path]
private lemma main
  {A : Type u} [CommRing A]
  {D : LevelModuliDatum.{u} A}
  {P P' : LevelModuliPackageAbs A D} :
-- imply
  ∃ e : P.B₀ ≃ₐ[A] P'.B₀, D.map (e : P.B₀ →ₐ[A] P'.B₀) P.univ = P'.univ := by
  classical
  let φ : P.B₀ →ₐ[A] P'.B₀ := P.classify P'.univ
  let ψ : P'.B₀ →ₐ[A] P.B₀ := P'.classify P.univ
  have hφ : D.map φ P.univ = P'.univ := P.map_classify P'.univ
  have hψ : D.map ψ P'.univ = P.univ := P'.map_classify P.univ
  have h1 : ψ.comp φ = AlgHom.id A P.B₀ := by
-- proof
    have hc : D.map (ψ.comp φ) P.univ = P.univ := by rw [D.map_comp, hφ, hψ]
    have hi : D.map (AlgHom.id A P.B₀) P.univ = P.univ := D.map_id _ _
    refine (P.classify_unique P.univ (ψ.comp φ) hc).trans (P.classify_unique P.univ (AlgHom.id A P.B₀) hi).symm
  have h2 : φ.comp ψ = AlgHom.id A P'.B₀ := by
    have hc : D.map (φ.comp ψ) P'.univ = P'.univ := by rw [D.map_comp, hψ, hφ]
    have hi : D.map (AlgHom.id A P'.B₀) P'.univ = P'.univ := D.map_id _ _
    refine (P'.classify_unique P'.univ (φ.comp ψ) hc).trans (P'.classify_unique P'.univ (AlgHom.id A P'.B₀) hi).symm
  refine ⟨AlgEquiv.ofAlgHom φ ψ h2 h1, ?_⟩
  exact hφ


-- created on 2026-10-23

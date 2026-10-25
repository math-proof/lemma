import Mathlib
import sympy.Basic
import Lemma.ModularCurve.LevelModuliPackage
import Lemma.ModularCurve.LevelModuliPackageAbs
import Lemma.Int.P2MUtil


/--
[ModularCurve_LevelModuliPackageAbs_exists_algEquiv_map_univ_eq_act](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_LevelModuliPackageAbs_exists_algEquiv_map_univ_eq_act.lean)
-/
@[path]
private lemma main
  {A : Type u} [CommRing A]
  {D : ModularCurve.LevelModuliDatum.{u} A}
  {P : ModularCurve.LevelModuliPackageAbs A D}
  {ρ ρ' : D.ProblemAut}
-- given
  (h₁ : ∀ (T : Type u) [CommRing T] [Algebra A T] (y : D.Pt T), ρ'.act (ρ.act y) = y)
  (h₂ : ∀ (T : Type u) [CommRing T] [Algebra A T] (y : D.Pt T), ρ.act (ρ'.act y) = y) :
-- imply
  ∃ σ : P.B₀ ≃ₐ[A] P.B₀,
      D.map (σ : P.B₀ →ₐ[A] P.B₀) P.univ = ρ.act P.univ ∧
      D.map (σ.symm : P.B₀ →ₐ[A] P.B₀) P.univ = ρ'.act P.univ := by
  classical
  let φ : P.B₀ →ₐ[A] P.B₀ := P.classify (ρ.act P.univ)
  let φ' : P.B₀ →ₐ[A] P.B₀ := P.classify (ρ'.act P.univ)
  have hφ : D.map φ P.univ = ρ.act P.univ := P.map_classify _
  have hφ' : D.map φ' P.univ = ρ'.act P.univ := P.map_classify _
  have hid : ∀ ψ : P.B₀ →ₐ[A] P.B₀, D.map ψ P.univ = P.univ → ψ = AlgHom.id A P.B₀ := by
-- proof
    intro ψ hψ
    rw [P.classify_unique P.univ ψ hψ, P.classify_unique P.univ (AlgHom.id A P.B₀) (D.map_id _ _)]
  have c1 : φ'.comp φ = AlgHom.id A P.B₀ := hid _ (by
    rw [D.map_comp, hφ, ← ρ.act_map, hφ', h₂])
  have c2 : φ.comp φ' = AlgHom.id A P.B₀ := hid _ (by
    rw [D.map_comp, hφ', ← ρ'.act_map, hφ, h₁])
  refine ⟨AlgEquiv.ofAlgHom φ φ' c2 c1, ?_, ?_⟩
  ·
    rwa [AlgEquiv.coe_algHom_ofAlgHom]
  ·
    rwa [AlgEquiv.ofAlgHom_symm, AlgEquiv.coe_algHom_ofAlgHom]


-- created on 2026-10-23

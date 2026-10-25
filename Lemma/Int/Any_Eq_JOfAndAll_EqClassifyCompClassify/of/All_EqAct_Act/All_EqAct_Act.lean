import Mathlib
import sympy.Basic
import Lemma.ModularCurve.LevelModuliPackage
import Lemma.ModularCurve.LevelModuliPackageAbs
import Lemma.Int.P2MUtil

open ModularCurve

/--
[ModularCurve_LevelModuliPackageAbs_exists_algEquiv_apply_jOf_univ_eq_classify_act_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_LevelModuliPackageAbs_exists_algEquiv_apply_jOf_univ_eq_classify_act_eq.lean)
-/
@[path]
private lemma main
  [CommRing A]
  {D : ModularCurve.LevelModuliDatum A}
  {P₀ : LevelModuliPackageAbs A D}
  {σ σ' : D.ProblemAut}
-- given
  (hσ : ∀ (T : Type) [CommRing T] [Algebra A T] (y : D.Pt T), σ'.act (σ.act y) = y)
  (hσ' : ∀ (T : Type) [CommRing T] [Algebra A T] (y : D.Pt T), σ.act (σ'.act y) = y) :
-- imply
  ∃ e : P₀.B₀ ≃ₐ[A] P₀.B₀,
      e (D.jOf P₀.univ) = D.jOf P₀.univ ∧
      ∀ (T : Type) [CommRing T] [Algebra A T] (x : D.Pt T),
        P₀.classify (σ.act x) = (P₀.classify x).comp (e : P₀.B₀ →ₐ[A] P₀.B₀) := by
-- proof
  set e : P₀.B₀ →ₐ[A] P₀.B₀ := P₀.classify (σ.act P₀.univ) with he
  set e' : P₀.B₀ →ₐ[A] P₀.B₀ := P₀.classify (σ'.act P₀.univ) with he'
  have hme : D.map e P₀.univ = σ.act P₀.univ := P₀.map_classify _
  have hme' : D.map e' P₀.univ = σ'.act P₀.univ := P₀.map_classify _
  have key : ∀ (φ ψ : P₀.B₀ →ₐ[A] P₀.B₀), D.map φ P₀.univ = D.map ψ P₀.univ → φ = ψ :=
    fun φ ψ h =>
      (P₀.classify_unique (D.map ψ P₀.univ) φ h).trans (P₀.classify_unique (D.map ψ P₀.univ) ψ rfl).symm
  have h1 : e.comp e' = AlgHom.id A P₀.B₀ := key _ _ (by
    rw [D.map_comp, hme', ← σ'.act_map, hme, hσ, D.map_id])
  have h2 : e'.comp e = AlgHom.id A P₀.B₀ := key _ _ (by
    rw [D.map_comp, hme, ← σ.act_map, hme', hσ', D.map_id])
  have hcoe : (AlgEquiv.ofAlgHom e e' h1 h2 : P₀.B₀ →ₐ[A] P₀.B₀) = e := AlgHom.ext fun _ => rfl
  refine ⟨AlgEquiv.ofAlgHom e e' h1 h2, ?_, ?_⟩
  ·
    change e (D.jOf P₀.univ) = D.jOf P₀.univ
    rw [← D.jOf_map, hme, σ.jOf_act]
  ·
    intro T _ _ x
    rw [hcoe]
    symm
    apply P₀.classify_unique
    rw [D.map_comp, hme, ← σ.act_map, P₀.map_classify]


-- created on 2026-10-23

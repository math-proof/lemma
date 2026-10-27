import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.RingTheory.GradedAlgebra.MultigradedBettiResolutionInvariance
open HomologicalComplex
open MetaMathlibExt


namespace MetaMathlibExt

/--
[multigradedBettiNumber_eq_of_resolutionComparison](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/GradedAlgebra/MultigradedBettiResolutionInvariance.lean)
-/
@[path]
lemma multigradedBettiNumber_eq_of_resolutionComparison
  {K : Type u} [Field K]
  {n : ℕ}
  {M : Type u} [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M] [Module K M]
  {targetGraded : MultigradedPolynomialModule K n M}
  {resolution₁ resolution₂ : CategoryTheory.ProjectiveResolution (ModuleCat.of (MvPolynomial (Fin n) K) M)}
  {ι₁ ι₂ : ℕ → Type u}
  {res₁ : MultigradedFreeResolution K n M targetGraded resolution₁ ι₁}
  {res₂ : MultigradedFreeResolution K n M targetGraded resolution₂ ι₂}
  {data₁ : MultigradedBaseChange targetGraded resolution₁ ι₁ res₁}
  {data₂ : MultigradedBaseChange targetGraded resolution₂ ι₂ res₂}
  {comparison : MultigradedResolutionComparison data₁ data₂}
  {α : Fin n →₀ Int}
  {i : ℕ} :
-- imply
  multigradedBettiNumber data₁ α i = multigradedBettiNumber data₂ α i := by
-- proof
  -- Install the `HasHomology` instances so that
  -- `HomotopyEquiv.quasiIsoAt_hom` supplies the `IsIso` used below.
  let _ := data₁.hasHom α i
  let _ := data₂.hasHom α i
  let e := comparison.componentHomotopyEquiv α
  have homIso :
    HomologicalComplex.homology (data₁.comp α) i ≅
      HomologicalComplex.homology (data₂.comp α) i := by
    exact CategoryTheory.asIso (HomologicalComplex.homologyMap e.hom i)
  have linEquiv :
    ↥(HomologicalComplex.homology (data₁.comp α) i) ≃ₗ[K]
      ↥(HomologicalComplex.homology (data₂.comp α) i) :=
    CategoryTheory.Iso.toLinearEquiv homIso
  have hFin := LinearEquiv.finrank_eq linEquiv
  unfold multigradedBettiNumber
  exact hFin

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26

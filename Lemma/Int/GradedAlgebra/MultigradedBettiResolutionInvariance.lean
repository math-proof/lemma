import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.GradedAlgebra.MultigradedBettiResolutionInvariance
open HomologicalComplex
open MetaMathlibExt


/--
[multigradedBettiNumber_eq_of_resolutionComparison](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/GradedAlgebra/MultigradedBettiResolutionInvariance.lean)
-/
@[path]
private lemma multigradedBettiNumber_eq_of_resolutionComparison_eq
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
  apply MetaMathlibExt.multigradedBettiNumber_eq_of_resolutionComparison comparison α i


-- created on 2026-10-20

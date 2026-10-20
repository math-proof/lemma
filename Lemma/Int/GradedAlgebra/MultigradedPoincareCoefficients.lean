import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.GradedAlgebra.MultigradedPoincareCoefficients
open MetaMathlibExt


/--
[multigradedPoincareCoefficients_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/GradedAlgebra/MultigradedPoincareCoefficients.lean)
-/
@[path]
private lemma multigradedPoincareCoefficients_apply_eq
  {K : Type u} [Field K]
  {n : ℕ}
  {M : Type u} [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M] [Module K M]
  {targetGraded : MultigradedPolynomialModule K n M}
  {resolution : CategoryTheory.ProjectiveResolution (ModuleCat.of (MvPolynomial (Fin n) K) M)}
  {ι : ℕ → Type u}
  {res : MultigradedFreeResolution K n M targetGraded resolution ι}
  {data : MultigradedBaseChange targetGraded resolution ι res}
  {i : ℕ}
  {α : Fin n →₀ Int} :
-- imply
  multigradedPoincareCoefficients data (i, α) =
    multigradedBettiNumber data α i := by
-- proof
  apply MetaMathlibExt.multigradedPoincareCoefficients_apply data i α

/--
[multigradedPoincareCoefficients_eq_of_resolutionComparison](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/GradedAlgebra/MultigradedPoincareCoefficients.lean)
-/
@[path]
private lemma multigradedPoincareCoefficients_eq_of_resolutionComparison_eq
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
  {comparison : MultigradedResolutionComparison data₁ data₂} :
-- imply
  multigradedPoincareCoefficients data₁ =
    multigradedPoincareCoefficients data₂ := by
-- proof
  apply MetaMathlibExt.multigradedPoincareCoefficients_eq_of_resolutionComparison comparison


-- created on 2026-10-20

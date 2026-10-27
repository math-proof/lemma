import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.RingTheory.GradedAlgebra.MultigradedPoincareCoefficients
open MetaMathlibExt


namespace MetaMathlibExt

/--
[multigradedPoincareCoefficients_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/GradedAlgebra/MultigradedPoincareCoefficients.lean)
-/
@[path]
lemma multigradedPoincareCoefficients_apply
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
    multigradedBettiNumber data α i :=
-- proof
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[multigradedPoincareCoefficients_eq_of_resolutionComparison](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/GradedAlgebra/MultigradedPoincareCoefficients.lean)
-/
@[path]
lemma multigradedPoincareCoefficients_eq_of_resolutionComparison
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
  funext p
  cases p with
  | mk i α =>
    unfold multigradedPoincareCoefficients
    exact multigradedBettiNumber_eq_of_resolutionComparison comparison α i

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26

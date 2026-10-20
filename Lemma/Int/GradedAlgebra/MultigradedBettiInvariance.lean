import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.GradedAlgebra.MultigradedBettiInvariance
open MetaMathlibExt


/--
[multigradedBettiNumber_eq_of_baseChange](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/GradedAlgebra/MultigradedBettiInvariance.lean)
-/
@[path]
private lemma multigradedBettiNumber_eq_of_baseChange_eq
  {K : Type u} [Field K]
  {n : ℕ}
  {M : Type u} [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M] [Module K M]
  {targetGraded : MultigradedPolynomialModule K n M}
  {resolution : CategoryTheory.ProjectiveResolution (ModuleCat.of (MvPolynomial (Fin n) K) M)}
  {ι : ℕ → Type u}
  {res : MultigradedFreeResolution K n M targetGraded resolution ι}
  {data₁ data₂ : MultigradedBaseChange targetGraded resolution ι res}
  {α : Fin n →₀ Int}
  {i : ℕ} :
-- imply
  multigradedBettiNumber data₁ α i = multigradedBettiNumber data₂ α i := by
-- proof
  apply MetaMathlibExt.multigradedBettiNumber_eq_of_baseChange data₁ data₂ α i


-- created on 2026-10-20

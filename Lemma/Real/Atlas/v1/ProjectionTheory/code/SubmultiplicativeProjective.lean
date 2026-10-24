import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ProjectionTheory.code.SubmultiplicativeProjective
open ProjectionTheory


/--
[proj_ratio_le_R_AD_proj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SubmultiplicativeProjective.lean)
-/
@[path]
private lemma proj_ratio_le_R_AD_proj_eq
  {δ : ℝ}
  {c : projConfigSpace.Config δ} :
-- imply
  projConfigSpace.ratio δ c ≤ R_AD_proj δ := by
-- proof
  apply ProjectionTheory.proj_ratio_le_R_AD_proj δ c

/--
[R_AD_proj_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SubmultiplicativeProjective.lean)
-/
@[path]
private lemma R_AD_proj_nonneg_eq
  {δ : ℝ} :
-- imply
  0 ≤ R_AD_proj δ := by
-- proof
  apply ProjectionTheory.R_AD_proj_nonneg δ

/--
[R_AD_proj_submultiplicative](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SubmultiplicativeProjective.lean)
-/
@[path]
private lemma R_AD_proj_submultiplicative_eq :
-- imply
  ∃ C : ℝ, 0 < C ∧ ∀ (δ₁ δ₂ : ℝ), 0 < δ₁ → δ₁ < 1 → 0 < δ₂ → δ₂ < 1 → R_AD_proj (δ₁ * δ₂) ≤ C * R_AD_proj δ₁ * R_AD_proj δ₂ := by
-- proof
  apply ProjectionTheory.R_AD_proj_submultiplicative


-- created on 2026-10-23

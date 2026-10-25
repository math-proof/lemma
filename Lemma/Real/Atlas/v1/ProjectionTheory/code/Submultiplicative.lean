import Mathlib
import sympy.Basic
import Structure.v1.Atlas.ProjectionTheory.code.Submultiplicative
open ProjectionTheory


/--
[ratio_factoring_axiom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/Submultiplicative.lean)
-/
@[path]
private lemma ratio_factoring_axiom_eq :
-- imply
  ∀ (δ₁ δ₂ : ℝ) (hδ₁ : 0 < δ₁) (hδ₁' : δ₁ < 1) (hδ₂ : 0 < δ₂) (hδ₂' : δ₂ < 1), ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ c : adConfigData.Config (δ₁ * δ₂), adConfigData.ratio (δ₁ * δ₂) c ≤ C * (δ₁ * δ₂)⁻¹ ^ ε * (adConfigData.ratio δ₁ (adConfigData.coarsen δ₁ δ₂ hδ₁ hδ₁' hδ₂ hδ₂' c) * adConfigData.ratio δ₂ (adConfigData.restrict δ₁ δ₂ hδ₁ hδ₁' hδ₂ hδ₂' c)) := by
-- proof
  apply ProjectionTheory.ratio_factoring_axiom

/--
[R_AD_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/Submultiplicative.lean)
-/
@[path]
private lemma R_AD_nonneg_eq
  {δ : ℝ} :
-- imply
  0 ≤ R_AD δ := by
-- proof
  apply ProjectionTheory.R_AD_nonneg δ

/--
[ratio_le_R_AD](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/Submultiplicative.lean)
-/
@[path]
private lemma ratio_le_R_AD_eq
  {δ : ℝ}
  {c : adConfigSpace.Config δ} :
-- imply
  adConfigSpace.ratio δ c ≤ R_AD δ := by
-- proof
  apply ProjectionTheory.ratio_le_R_AD δ c

/--
[R_AD_submultiplicative](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/Submultiplicative.lean)
-/
@[path]
private lemma R_AD_submultiplicative_eq
  {δ₁ δ₂ : ℝ}
-- given
  (hδ₁ : 0 < δ₁)
  (hδ₁' : δ₁ < 1)
  (hδ₂ : 0 < δ₂)
  (hδ₂' : δ₂ < 1) :
-- imply
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ R_AD (δ₁ * δ₂) ≤ C * (δ₁ * δ₂)⁻¹ ^ ε * (R_AD δ₁ * R_AD δ₂) := by
-- proof
  apply ProjectionTheory.R_AD_submultiplicative δ₁ δ₂ hδ₁ hδ₁' hδ₂ hδ₂'


-- created on 2026-10-23

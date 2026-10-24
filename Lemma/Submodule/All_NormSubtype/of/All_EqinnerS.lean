import Mathlib
import sympy.Basic


/--
[norm_of_inner_preserving](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/InfinitesimalEquivalenceProposition71.lean)
-/
@[path]
private lemma main
  [NormedAddCommGroup V₁]
  [InnerProductSpace ℂ V₁]
  [NormedAddCommGroup V₂]
  [InnerProductSpace ℂ V₂]
  {S₁ : Submodule ℂ V₁}
  {S₂ : Submodule ℂ V₂}
  {A : S₁ ≃ₗ[ℂ] S₂}
-- given
  (h_inner : ∀ (x y : S₁), @inner ℂ V₂ _ (S₂.subtype (A x)) (S₂.subtype (A y)) = @inner ℂ V₁ _ (S₁.subtype x) (S₁.subtype y)) :
-- imply
  ∀ x : S₁, ‖S₂.subtype (A x)‖ = ‖S₁.subtype x‖ := by
-- proof
  intro x
  have h := h_inner x x
  have h1 := inner_self_eq_norm_sq (𝕜 := ℂ) (S₂.subtype (A x))
  have h2 := inner_self_eq_norm_sq (𝕜 := ℂ) (S₁.subtype x)
  have h3 : RCLike.re (@inner ℂ V₂ _ (S₂.subtype (A x)) (S₂.subtype (A x))) =
    RCLike.re (@inner ℂ V₁ _ (S₁.subtype x) (S₁.subtype x)) := by rw [h]
  rw [h1, h2] at h3
  have ha : (0 : ℝ) ≤ ‖S₂.subtype (A x)‖ := norm_nonneg _
  have hb : (0 : ℝ) ≤ ‖S₁.subtype x‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖S₂.subtype (A x)‖ - ‖S₁.subtype x‖)]


-- created on 2026-10-23
-- updated on 2026-10-24

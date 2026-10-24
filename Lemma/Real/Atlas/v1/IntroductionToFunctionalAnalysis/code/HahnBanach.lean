import Mathlib
import sympy.Basic
open Submodule

/--
[zorns_lemma](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/HahnBanach.lean)
-/
@[path]
lemma zorns_lemma
  [Preorder α]
-- given
  (h : ∀ c : Set α, IsChain (· ≤ ·) c → BddAbove c) :
-- imply
  ∃ m : α, IsMax m :=
-- proof
  zorn_le h

/--
[hahn_banach_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/HahnBanach.lean)
-/
@[path]
lemma hahn_banach_theorem
  {𝕜 : Type*}
  [RCLike 𝕜]
  {E : Type*}
  [SeminormedAddCommGroup E]
  [NormedSpace 𝕜 E]
  (M : Subspace 𝕜 E)
  (f : StrongDual 𝕜 M) :
-- imply
  ∃ F : StrongDual 𝕜 E, (∀ m : M, F m = f m) ∧ ‖F‖ = ‖f‖ :=
-- proof
  exists_extension_norm_eq M f

/--
[exists_norm_one_functional_achieving_norm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/HahnBanach.lean)
-/
@[path]
lemma exists_norm_one_functional_achieving_norm
  {𝕜 : Type*}
  [RCLike 𝕜]
  {V : Type*}
  [NormedAddCommGroup V]
  [NormedSpace 𝕜 V]
  {v : V}
-- given
  (hv : v ≠ 0) :
-- imply
  ∃ f : StrongDual 𝕜 V, ‖f‖ = 1 ∧ f v = ↑‖v‖ :=
-- proof
  exists_dual_vector 𝕜 v (norm_ne_zero_iff.mpr hv)

/--
[hahn_banach_one_step_extension_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/HahnBanach.lean)
-/
@[path]
lemma hahn_banach_one_step_extension_bound
  {𝕜 : Type*}
  [RCLike 𝕜]
  {E : Type*}
  [SeminormedAddCommGroup E]
  [NormedSpace 𝕜 E]
  {M : Subspace 𝕜 E}
  {f : StrongDual 𝕜 M}
  {C : ℝ}
  {x₀ : E}
-- given
  (hC : 0 ≤ C)
  (hf_bound : ∀ m : M, ‖f m‖ ≤ C * ‖(m : E)‖)
  (hx₀ : x₀ ∉ M) :
-- imply
  ∃ g : StrongDual 𝕜 ↥(M ⊔ 𝕜 ∙ x₀),
    (∀ m : M, g ⟨↑m, mem_sup_left m.2⟩ = f m) ∧
    (∀ v : ↥(M ⊔ 𝕜 ∙ x₀), ‖g v‖ ≤ C * ‖(v : E)‖) ∧
    M < M ⊔ 𝕜 ∙ x₀ := by
-- proof
  obtain ⟨G, hG_ext, hG_norm⟩ := exists_extension_norm_eq M f
  let M' := M ⊔ 𝕜 ∙ x₀
  let g : StrongDual 𝕜 ↥M' := G.comp M'.subtypeL
  refine ⟨g, ?_, ?_, ?_⟩
  · intro m
    simp only [g, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
    exact hG_ext m
  · intro v
    simp only [g, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
    have hG_le : ‖G‖ ≤ C := by
      rw [hG_norm]
      exact ContinuousLinearMap.opNorm_le_bound f hC hf_bound
    calc ‖G (v : E)‖
        ≤ ‖G‖ * ‖(v : E)‖ := G.le_opNorm (v : E)
      _ ≤ C * ‖(v : E)‖ := mul_le_mul_of_nonneg_right hG_le (norm_nonneg _)
  · apply lt_of_le_of_ne le_sup_left
    intro h
    apply hx₀
    have : x₀ ∈ (M ⊔ 𝕜 ∙ x₀ : Submodule 𝕜 E) :=
      mem_sup_right (mem_span_singleton_self x₀)
    rwa [← h] at this


-- created on 2026-10-23
-- updated on 2026-10-24

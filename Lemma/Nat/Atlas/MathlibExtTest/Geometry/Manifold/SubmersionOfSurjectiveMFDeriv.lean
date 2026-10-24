import Mathlib
import sympy.Basic
import sympy.atlas.MathlibExtTest.Geometry.Manifold.SubmersionOfSurjectiveMFDeriv
open MathlibExt.Geometry.Manifold.SubmersionOfSurjectiveMFDerivWanted MathlibExtTest MathlibExtTest.Geometry MathlibExtTest.Geometry.Manifold MathlibExtTest.Geometry.Manifold.SubmersionOfSurjectiveMFDeriv
open scoped ContDiff Manifold Topology


namespace MathlibExtTest.Geometry.Manifold.SubmersionOfSurjectiveMFDeriv

/--
[sqNorm_isSubmersionAt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Geometry/Manifold/SubmersionOfSurjectiveMFDeriv.lean)
-/
@[path]
lemma sqNorm_isSubmersionAt
  {p₀ : ℝ × ℝ × ℝ}
-- given
  (hp₀ : p₀ ≠ 0) :
-- imply
  Manifold.IsSubmersionAt 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ) (∞ : ℕ∞ω) (fun p : ℝ × ℝ × ℝ ↦ p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) p₀ := by
-- proof
  apply submersionAt_of_surjective_mfderiv (n := (∞ : ℕ∞ω))
  · simp
  · filter_upwards with y
    exact (show ContDiffAt ℝ (∞ : ℕ∞ω)
      (fun p : ℝ × ℝ × ℝ ↦ p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) y by
      fun_prop).contMDiffAt
  · let A : (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
    ((2 * p₀.1) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) +
      (2 * p₀.2.1) •
        (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
          (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) +
      (2 * p₀.2.2) •
        (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
          (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))
    have h :=
      (((hasFDerivAt_fst (𝕜 := ℝ) (p := p₀)).pow 2).add
        (((hasFDerivAt_fst (𝕜 := ℝ) (p := p₀.2)).comp p₀
          (hasFDerivAt_snd (𝕜 := ℝ) (p := p₀))).pow 2)).add
        (((hasFDerivAt_snd (𝕜 := ℝ) (p := p₀.2)).comp p₀
          (hasFDerivAt_snd (𝕜 := ℝ) (p := p₀))).pow 2)
    have hderiv : HasFDerivAt
      (fun p : ℝ × ℝ × ℝ ↦ p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) A p₀ := by
      convert h using 1
      · funext p
        rfl
      · simp [A, Function.comp_apply]
    have hA (v : ℝ × ℝ × ℝ) :
      A v = 2 * (p₀.1 * v.1 + p₀.2.1 * v.2.1 + p₀.2.2 * v.2.2) := by
      simp [A]
      ring
    rw [mfderiv_eq_fderiv, hderiv.fderiv]
    change Function.Surjective A
    intro y
    by_cases h₁ : p₀.1 = 0
    · by_cases h₂ : p₀.2.1 = 0
      · have h₃ : p₀.2.2 ≠ 0 := by
        intro h₃
        exact hp₀ (Prod.ext h₁ (Prod.ext h₂ h₃))
        refine ⟨(0, 0, y / (2 * p₀.2.2)), ?_⟩
        rw [hA]
        field_simp
        ring
      · refine ⟨(0, y / (2 * p₀.2.1), 0), ?_⟩
        rw [hA]
        field_simp
        ring
    · refine ⟨(y / (2 * p₀.1), 0, 0), ?_⟩
      rw [hA]
      field_simp
      ring

end MathlibExtTest.Geometry.Manifold.SubmersionOfSurjectiveMFDeriv


-- created on 2026-10-23

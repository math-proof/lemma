/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Geometry/Manifold/SubmersionOfSurjectiveMFDeriv.lean -/


import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Def.Geometry.Manifold.SubmersionOfSurjectiveMFDeriv
import Lemma.Set.Manifold.SubmersionOfSurjectiveMFDeriv
open scoped ContDiff Manifold Topology
open MathlibExt.Geometry.Manifold.SubmersionOfSurjectiveMFDerivWanted


namespace MathlibExtTest.Geometry.Manifold.SubmersionOfSurjectiveMFDeriv

-- The public criterion proves multiplication is a smooth submersion at (1, 0).
example : Manifold.IsSubmersionAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) (∞ : ℕ∞ω)
    (fun p : ℝ × ℝ ↦ p.1 * p.2) (1, 0) := by
  apply Manifold.IsSubmersionAt.of_surjective_mfderiv (n := (∞ : ℕ∞ω))
  · simp
  · filter_upwards with y
    exact (show ContDiffAt ℝ (∞ : ℕ∞ω) (fun p : ℝ × ℝ ↦ p.1 * p.2) y by
      fun_prop).contMDiffAt
  · have hderiv : HasFDerivAt (fun p : ℝ × ℝ ↦ p.1 * p.2)
        (ContinuousLinearMap.snd ℝ ℝ ℝ) (1, 0) := by
      have h :=
        (hasFDerivAt_fst (𝕜 := ℝ) (p := ((1, 0) : ℝ × ℝ))).mul
          (hasFDerivAt_snd (𝕜 := ℝ) (p := ((1, 0) : ℝ × ℝ)))
      convert h using 1
      simp
    rw [mfderiv_eq_fderiv, hderiv.fderiv]
    intro y
    exact ⟨(0, y), rfl⟩

-- The frozen theorem applies to a nonlinear map whose derivative at the origin is projection.
example : Manifold.IsSubmersionAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) (∞ : ℕ∞ω)
    (fun p : ℝ × ℝ ↦ p.1 ^ 2 + p.2) (0, 0) := by
  apply submersionAt_of_surjective_mfderiv (n := (∞ : ℕ∞ω))
  · simp
  · filter_upwards with y
    exact (show ContDiffAt ℝ (∞ : ℕ∞ω) (fun p : ℝ × ℝ ↦ p.1 ^ 2 + p.2) y by
      fun_prop).contMDiffAt
  · have hderiv : HasFDerivAt (fun p : ℝ × ℝ ↦ p.1 ^ 2 + p.2)
        (ContinuousLinearMap.snd ℝ ℝ ℝ) (0, 0) := by
      have h :=
        ((hasFDerivAt_fst (𝕜 := ℝ) (p := ((0, 0) : ℝ × ℝ))).pow 2).add
          (hasFDerivAt_snd (𝕜 := ℝ) (p := ((0, 0) : ℝ × ℝ)))
      convert h using 1
      simp
    rw [mfderiv_eq_fderiv, hderiv.fderiv]
    intro y
    exact ⟨(0, y), rfl⟩

-- Openness makes the squared norm a submersion throughout a neighbourhood of p₀.
example (p₀ : ℝ × ℝ × ℝ) (hp₀ : p₀ ≠ 0) :
    ∀ᶠ p in 𝓝 p₀,
      Manifold.IsSubmersionAt 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ) (∞ : ℕ∞ω)
        (fun q : ℝ × ℝ × ℝ ↦ q.1 ^ 2 + q.2.1 ^ 2 + q.2.2 ^ 2) p := by
  exact isOpen_isSubmersionAt.mem_nhds (sqNorm_isSubmersionAt p₀ hp₀)

end MathlibExtTest.Geometry.Manifold.SubmersionOfSurjectiveMFDeriv

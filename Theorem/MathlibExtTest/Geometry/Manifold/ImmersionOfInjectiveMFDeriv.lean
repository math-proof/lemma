/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Geometry/Manifold/ImmersionOfInjectiveMFDeriv.lean -/


import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Theorem.Geometry.Manifold.ImmersionOfInjectiveMFDeriv
import Lemma.Set.Manifold.ImmersionOfInjectiveMFDeriv
open scoped Topology ContDiff
open Manifold
open MathlibExt.Geometry.Manifold.ImmersionOfInjectiveMFDerivWanted


noncomputable section

namespace MathlibExtTest.Geometry.Manifold.ImmersionOfInjectiveMFDeriv

-- The parabola has a computed injective differential and finite-dimensional complemented range.
example :
    IsImmersionAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun t : ℝ => (t, t ^ 2)) 1 := by
  apply IsImmersionAt.of_injective_mfderiv_of_closedComplemented_range (n := ∞)
    (by simp)
  · exact Filter.Eventually.of_forall fun _ =>
      contMDiffAt_iff_contDiffAt.mpr <| by
        simpa [pow_two] using
          contDiffAt_id.prodMk (contDiffAt_id.mul contDiffAt_id)
  · have hparabola :
        HasFDerivAt (fun t : ℝ => (t, t ^ 2))
          ((ContinuousLinearMap.id ℝ ℝ).prod
            ((1 : ℝ) • ContinuousLinearMap.id ℝ ℝ +
              (1 : ℝ) • ContinuousLinearMap.id ℝ ℝ)) 1 := by
      simpa [pow_two] using
        (hasFDerivAt_id (𝕜 := ℝ) (1 : ℝ)).prodMk
          ((hasFDerivAt_id (𝕜 := ℝ) (1 : ℝ)).mul
            (hasFDerivAt_id (𝕜 := ℝ) (1 : ℝ)))
    rw [mfderiv_eq_fderiv, hparabola.fderiv]
    intro u v huv
    change ℝ at u v
    change (u : ℝ) = v
    have hfirst := congrArg Prod.fst huv
    change u = v at hfirst
    exact hfirst
  · let L : ℝ →L[ℝ] ℝ × ℝ :=
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) (fun t : ℝ => (t, t ^ 2)) 1 :
        ℝ →L[ℝ] ℝ × ℝ)
    change L.range.ClosedComplemented
    exact Submodule.ClosedComplemented.of_finiteDimensional _

-- The graph differential keeps both input coordinates, so its computed map is injective.
example (p₀ : ℝ × ℝ) :
    IsImmersionAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) ∞
      (fun p : ℝ × ℝ => (p.1, p.2, p.1 * p.2)) p₀ := by
  apply immersionAt_of_injective_mfderiv (n := ∞) (by simp)
  · exact Filter.Eventually.of_forall fun _ =>
      contMDiffAt_iff_contDiffAt.mpr <|
        contDiffAt_fst.prodMk
          (contDiffAt_snd.prodMk (contDiffAt_fst.mul contDiffAt_snd))
  · have hgraph :
        HasFDerivAt (fun p : ℝ × ℝ => (p.1, p.2, p.1 * p.2))
          ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
            ((ContinuousLinearMap.snd ℝ ℝ ℝ).prod
              (p₀.1 • ContinuousLinearMap.snd ℝ ℝ ℝ +
                p₀.2 • ContinuousLinearMap.fst ℝ ℝ ℝ))) p₀ := by
      simpa only [Pi.mul_apply] using
        (hasFDerivAt_fst (𝕜 := ℝ) (p := p₀)).prodMk
          ((hasFDerivAt_snd (𝕜 := ℝ) (p := p₀)).prodMk
            ((hasFDerivAt_fst (𝕜 := ℝ) (p := p₀)).mul
              (hasFDerivAt_snd (𝕜 := ℝ) (p := p₀))))
    rw [mfderiv_eq_fderiv, hgraph.fderiv]
    intro u v huv
    change ℝ × ℝ at u v
    change (u : ℝ × ℝ) = v
    apply Prod.ext
    · have hfirst := congrArg (fun q => q.1) huv
      change u.1 = v.1 at hfirst
      exact hfirst
    · have hsecond := congrArg (fun q => q.2.1) huv
      change u.2 = v.2 at hsecond
      exact hsecond

-- Mathlib's immersion API exposes the circle parametrisation's injective manifold differential.
example (t₀ : ℝ) :
    Function.Injective
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ)
        (fun t : ℝ => (Real.cos t, Real.sin t)) t₀) := by
  exact (circle_isImmersionAt t₀).injective_mfderiv (by simp)

end MathlibExtTest.Geometry.Manifold.ImmersionOfInjectiveMFDeriv
end

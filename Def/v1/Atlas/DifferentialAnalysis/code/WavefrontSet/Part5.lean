/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Distribution.Support
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Fourier.Convolution
import Def.v1.Atlas.DifferentialAnalysis.code.DifferentialOperators.Part2
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.DifferentialOperators
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.HormanderFundamental
import Def.v1.Atlas.DifferentialAnalysis.code.HormanderFundamental
import Theorem.v1.Atlas.DifferentialAnalysis.code.WavefrontSet.Part2


noncomputable section

open scoped SchwartzMap FourierTransform

open MeasureTheory Set

namespace ConeSupport

variable {n : ℕ}

variable {n}

/-- Boundary points of the closed ball are spherical directions. -/
def ClosedBall.toSphere (p : ClosedBall n) (hp : ‖p.val‖ = 1) : ConeSupport.Sphere n :=
  ⟨p.val, by simp [Metric.mem_sphere, dist_zero_right, hp]⟩

/-- Interior points of the closed ball map back to Euclidean space via the
"de-compactification" formula `p ↦ (1 - ‖p‖)⁻¹ p`. -/
def ClosedBall.toEuclidean (p : ClosedBall n) (hp : ‖p.val‖ < 1) :
    EuclideanSpace ℝ (Fin n) :=
  (1 - ‖p.val‖)⁻¹ • p.val

/-- The conic singular support `Css u` on the closed ball: at boundary points it agrees
with the spherical conic singular support, at interior points (after de-compactification)
it agrees with the usual singular support. -/
def Css (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : Set (ClosedBall n) :=
  {p | if h : ‖p.val‖ = 1 then
        p.toSphere h ∈ ConeSupport.ConicSingularSupportSphere u
       else

        have hp : ‖p.val‖ < 1 := lt_of_le_of_ne p.property h
        p.toEuclidean hp ∈ ConeSupport.singularSupport u}

/-- The cone support `Csp u` on the closed ball: at boundary points it agrees with the
spherical cone support, at interior points (after de-compactification) it agrees with the
distributional support of `u`. -/
def Csp (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : Set (ClosedBall n) :=
  {p | if h : ‖p.val‖ = 1 then
        p.toSphere h ∈ ConeSupport.ConeSupportSphere u
       else
        have hp : ‖p.val‖ < 1 := lt_of_le_of_ne p.property h
        p.toEuclidean hp ∈ Distribution.dsupport u}

/-- Bundled statement: `Csp u`, `Css u`, and their sphere analogues are all closed; and a
"disjoint Css ⇒ Schwartz" statement holds. -/
def WFsc (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    Set (ClosedBall n × ClosedBall n) :=
  {pq | ¬ (
    if h : ‖pq.1.val‖ = 1 then

      ∃ (g : ConeSupport.E n → ℂ),
        ConeSupport.IsConicCutoffNear g (pq.1.toSphere h) ∧
        pq.2 ∉ Css (𝓕 (TemperedDistribution.smulLeftCLM ℂ g u))
    else

      have hp : ‖pq.1.val‖ < 1 := lt_of_le_of_ne pq.1.property h
      ∃ (φ : ConeSupport.E n → ℂ),
        ContDiff ℝ ↑(⊤ : ℕ∞) φ ∧
        HasCompactSupport φ ∧
        φ (pq.1.toEuclidean hp) ≠ 0 ∧
        pq.2 ∉ Css (𝓕 (TemperedDistribution.smulLeftCLM ℂ φ u))
    )}

/-- A function `f : E → F` is positively homogeneous of degree `d : ℤ` if
`f (a • x) = a^d • f x` for every `a > 0` and every nonzero `x`. -/
def IsPositivelyHomogeneous (d : ℤ) (f : E → F) : Prop :=
  ∀ (a : ℝ), 0 < a → ∀ (x : E), x ≠ 0 → f (a • x) = (a : ℝ) ^ d • f x

/-- The scaling continuous linear equivalence `E ≃L[ℝ] E` corresponding to a nonzero
scalar `a`; the action is `x ↦ a • x`. -/
noncomputable def scaleCLE (a : ℝ) (ha : a ≠ 0) : E ≃L[ℝ] E :=
  Units.mk0 a ha • ContinuousLinearEquiv.refl ℝ E

end ConeSupport
end

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
import Abbrev.v1.Atlas.DifferentialAnalysis.code.WavefrontSet


noncomputable section

open scoped SchwartzMap FourierTransform

open MeasureTheory Set

namespace ConeSupport

variable {n : ℕ}

/-- `IsConicCutoffNear g ω` says that `g : ℝⁿ → ℂ` is a smooth conic cutoff function
adapted to a unit-sphere direction `ω`. Concretely: `g` is `C^∞`, vanishes near the
origin, and agrees outside some small ball with a degree-`0` positively homogeneous
function `ψ` that does not vanish at `ω`. -/
def IsConicCutoffNear (g : E n → ℂ) (ω : Sphere n) : Prop :=
  ContDiff ℝ ↑(⊤ : ℕ∞) g ∧
  ∃ (R : ℝ), 0 < R ∧ R < 1 ∧
    ∃ (R₀ : ℝ), 0 < R₀ ∧ Function.support g ⊆ {x : E n | R₀ ≤ ‖x‖} ∧
    ∃ (ψ : E n → ℂ),
      (∀ (a : ℝ), 0 < a → ∀ (x : E n), x ≠ 0 → ψ (a • x) = ψ x) ∧
      ψ (ω : E n) ≠ 0 ∧
      (∀ x : E n, R < ‖x‖ → g x = ψ x)

/-- The *cone support on the sphere* of a tempered distribution `u`: the directions
`ω` at infinity for which no conic cutoff `g` near `ω` kills `u`, i.e., for which
`g · u ≠ 0` for every conic cutoff. -/
def ConeSupportSphere (u : 𝓢'(E n, ℂ)) : Set (Sphere n) :=
  {ω | ¬ ∃ (g : E n → ℂ), IsConicCutoffNear g ω ∧
         TemperedDistribution.smulLeftCLM ℂ g u = 0}

/-- `IsSmoothNear u x` says that `u` is *smooth near `x`*: there exists a smooth
compactly supported `φ` with `φ x ≠ 0` such that `φ · u` is (the embedding of) a
Schwartz function. This is the local Schwartz-representation criterion. -/
def IsSmoothNear (u : 𝓢'(E n, ℂ)) (x : E n) : Prop :=
  ∃ (φ : E n → ℂ),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧
    HasCompactSupport φ ∧
    φ x ≠ 0 ∧
    ∃ (f : SchwartzMap (E n) ℂ),
      TemperedDistribution.smulLeftCLM ℂ φ u = (f : 𝓢'(E n, ℂ))

/-- The *singular support* of `u` (classical, in the interior): the set of points
`x` at which `u` fails to be smooth, in the sense of `IsSmoothNear`. -/
def singularSupport (u : 𝓢'(E n, ℂ)) : Set (E n) :=
  {x | ¬ IsSmoothNear u x}

/-- The *conic singular support on the sphere*: directions `ω` for which no conic
cutoff `g` near `ω` makes `g · u` (the embedding of) a Schwartz function. This is
the asymptotic singular support of `u` at infinity. -/
def ConicSingularSupportSphere (u : 𝓢'(E n, ℂ)) : Set (Sphere n) :=
  {ω | ¬ ∃ (g : E n → ℂ), IsConicCutoffNear g ω ∧
         ∃ (f : SchwartzMap (E n) ℂ),
           TemperedDistribution.smulLeftCLM ℂ g u = (f : 𝓢'(E n, ℂ))}

/-- The *cone support* of `u`, packaged as a subset of `ℝⁿ ⊕ S^{n-1}`: the
distributional support in the interior, together with the cone support on the
sphere at infinity. -/
def coneSupport (u : 𝓢'(E n, ℂ)) : Set (E n ⊕ Sphere n) :=
  Sum.inl '' (Distribution.dsupport u) ∪ Sum.inr '' (ConeSupportSphere u)

/-- The *cone singular support* of `u`, packaged as a subset of `ℝⁿ ⊕ S^{n-1}`:
the singular support in the interior, plus the conic singular support on the
sphere at infinity. -/
def coneSingularSupport (u : 𝓢'(E n, ℂ)) : Set (E n ⊕ Sphere n) :=
  Sum.inl '' (singularSupport u) ∪ Sum.inr '' (ConicSingularSupportSphere u)

/-- The (classical) *wavefront set* of `u`: the set of pairs `(x, ω)` such
that no smooth compactly supported bump `φ` nonzero at `x` produces a
distribution `φ · u` whose Fourier transform is conically smooth at `ω`. -/
def wavefrontSet (u : 𝓢'(E n, ℂ)) : Set (E n × Sphere n) :=
  {p | ¬ ∃ (φ : E n → ℂ),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧
    HasCompactSupport φ ∧
    φ p.1 ≠ 0 ∧
    p.2 ∉ ConicSingularSupportSphere (𝓕 (TemperedDistribution.smulLeftCLM ℂ φ u))}

/-- The *scattering wavefront set at infinity*: the contribution to the
wavefront set parametrised by sphere directions at infinity, with the second
factor in the cone singular support of `𝓕 (g · u)`. -/
def scatteringWavefrontSetAtInfinity (u : 𝓢'(E n, ℂ)) : Set (Sphere n × (E n ⊕ Sphere n)) :=
  {q | ¬ ∃ (g : E n → ℂ), IsConicCutoffNear g q.1 ∧
    q.2 ∉ coneSingularSupport (𝓕 (TemperedDistribution.smulLeftCLM ℂ g u))}

/-- The *scattering wavefront set* of a tempered distribution `u`, obtained
by combining the classical wavefront set with the wavefront set at infinity. -/
def scatteringWavefrontSet (u : 𝓢'(E n, ℂ)) : Set ((E n ⊕ Sphere n) × (E n ⊕ Sphere n)) :=
  (Prod.map Sum.inl Sum.inr '' wavefrontSet u) ∪
  (Prod.map Sum.inr id '' scatteringWavefrontSetAtInfinity u)

/-- The *conic support on the sphere* (duplicated definition kept for
backward-compatibility with earlier statements). -/
def ConicSupportSphere (u : 𝓢'(E n, ℂ)) : Set (Sphere n) :=
  {ω | ¬ ∃ (g : E n → ℂ), IsConicCutoffNear g ω ∧
         TemperedDistribution.smulLeftCLM ℂ g u = 0}

/-- A tempered distribution `u` is *compactly supported* if it vanishes on any
Schwartz function whose support is disjoint from some compact set `K`. -/
def IsCompactlySupportedDistribution (u : 𝓢'(E n, ℂ)) : Prop :=
  ∃ K : Set (E n), IsCompact K ∧
    ∀ f : 𝓢(E n, ℂ), (Function.support (⇑f) ∩ K = ∅) → u f = 0

/-- The *direction* of a nonzero vector `x ∈ ℝⁿ`, namely `x / ‖x‖` viewed as
a point of the unit sphere. -/
def directionOf {n : ℕ} (x : E n) (hx : x ≠ 0) : Sphere n :=
  ⟨‖x‖⁻¹ • x, by
    simp [Metric.mem_sphere, dist_zero_right, norm_smul, abs_of_pos (inv_pos.mpr
      (norm_pos_iff.mpr hx)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩


end ConeSupport
end

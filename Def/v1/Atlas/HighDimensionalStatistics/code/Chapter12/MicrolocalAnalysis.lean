/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter12/MicrolocalAnalysis.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.TemperedDistribution
import Abbrev.v1.Atlas.HighDimensionalStatistics.code.Chapter12.MicrolocalAnalysis
set_option maxHeartbeats 800000


noncomputable section

open scoped SchwartzMap FourierTransform Pointwise

open MeasureTheory Set Filter

variable {n : ℕ}

namespace Chapter12

/-- `f` is homogeneous of degree `k` outside the unit ball: for `t > 0` and
`‖x‖ ≥ 1`, `f(tx) = t^k f(x)`. -/
def IsHomogeneousOutside (f : Rn n → ℂ) (k : ℤ) : Prop :=
  ∀ (t : ℝ) (x : Rn n), 0 < t → 1 ≤ ‖x‖ → f (t • x) = (t : ℂ) ^ k * f x

/-- `Γ` is a cone if it is invariant under positive scalar multiplication. -/
def IsCone (Γ : Set (Rn n)) : Prop :=
  ∀ (t : ℝ) (ξ : Rn n), 0 < t → ξ ∈ Γ → t • ξ ∈ Γ

/-- `g` is rapidly decreasing: for every `N` there is a constant `C` with
`‖g ξ‖ ≤ C (1 + ‖ξ‖)⁻ᴺ`. -/
def IsRapidlyDecreasing (g : Rn n → ℂ) : Prop :=
  ∀ (N : ℕ), ∃ (C : ℝ), 0 < C ∧ ∀ (ξ : Rn n), ‖g ξ‖ ≤ C * (1 + ‖ξ‖)⁻¹ ^ N

/-- `f` is homogeneous of degree zero away from the origin: `f(tx) = f(x)` for
`t > 0` and `x ≠ 0`. -/
def IsHomogeneousDegZero (f : Rn n → ℂ) : Prop :=
  ∀ (t : ℝ) (x : Rn n), 0 < t → x ≠ 0 → f (t • x) = f x

/-- The conic support of `u`: nonzero directions `ξ` such that every smooth
conic-cutoff with `φ(ξ) ≠ 0` produces a nonzero distribution `φ u`. -/
def ConeSupport (n : ℕ) (u : 𝓢'(Rn n, ℂ)) : Set (Rn n) :=
  {ξ : Rn n | ξ ≠ 0 ∧
    ∀ (φ : Rn n → ℂ), ContDiff ℝ ⊤ φ → IsHomogeneousOutside φ 0 → φ ξ ≠ 0 →
      TemperedDistribution.smulLeftCLM ℂ φ u ≠ 0}

/-- The conic singular support of `u`: nonzero directions `ξ` such that no
conic-cutoff with `φ(ξ) ≠ 0` makes `φ u` Schwartz. -/
def ConeSingularSupport (n : ℕ) (u : 𝓢'(Rn n, ℂ)) : Set (Rn n) :=
  {ξ : Rn n | ξ ≠ 0 ∧
    ∀ (φ : Rn n → ℂ), ContDiff ℝ ⊤ φ → IsHomogeneousOutside φ 0 → φ ξ ≠ 0 →
      TemperedDistribution.smulLeftCLM ℂ φ u ∉
        Set.range (SchwartzMap.toTemperedDistributionCLM (Rn n) ℂ)}

end Chapter12
end

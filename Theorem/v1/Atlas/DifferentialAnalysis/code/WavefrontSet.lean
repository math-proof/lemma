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
import Def.v1.Atlas.DifferentialAnalysis.code.WavefrontSet.Part2


noncomputable section

open scoped SchwartzMap FourierTransform

open MeasureTheory Set

namespace ConeSupport

variable {n : ℕ}

/-- "Open neighbourhood" formulation of the wavefront set complement: if `(x₀, ω₀)` is not
in `WF(u)`, there are open neighbourhoods `U ∋ x₀` and `V ∋ ω₀` such that for every cutoff
`φ'` supported in `U`, `V` is disjoint from `Css (𝓕 (φ' · u))`. -/
theorem exists_conicCutoff (ω : Sphere n) :
    ∃ (g : E n → ℂ), IsConicCutoffNear g ω := by

  let χ : ContDiffBump (0 : E n) := ⟨1/3, 2/3, by positivity, by norm_num⟩
  refine ⟨fun x => Complex.ofReal (1 - χ x), ?_, 2/3, by positivity, by norm_num,
    1/3, by positivity, ?_, fun _ => 1, ?_, ?_, ?_⟩
  ·
    rw [contDiff_infty]
    intro k
    exact_mod_cast Complex.ofRealCLM.contDiff.comp (contDiff_const.sub χ.contDiff)

  ·
    intro x hx
    simp only [Function.mem_support] at hx
    simp only [Set.mem_setOf_eq]
    by_contra h
    simp only [not_le] at h
    have hx_ball : x ∈ Metric.closedBall (0 : E n) χ.rIn := by
      simp only [Metric.mem_closedBall, dist_zero_right]
      exact le_of_lt h
    have : χ x = 1 := χ.one_of_mem_closedBall hx_ball
    simp only [this, sub_self, Complex.ofReal_zero] at hx
    exact hx rfl
  ·
    intro a _ x _; rfl
  ·
    exact one_ne_zero
  ·
    intro x hx
    have hx_out : χ.rOut ≤ dist x 0 := by
      simp only [dist_zero_right]; exact le_of_lt hx
    have : χ x = 0 := χ.zero_of_le_dist hx_out
    simp only [this, sub_zero, Complex.ofReal_one]

end ConeSupport
end

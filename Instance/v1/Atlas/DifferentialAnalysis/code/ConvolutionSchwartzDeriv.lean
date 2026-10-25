/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConvolutionSchwartzDeriv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
open MeasureTheory Filter Topology Metric Set
open scoped ZeroAtInfty ContDiff


noncomputable section

namespace ConvolutionDensity

variable {n : ℕ}

/-- The cocompact filter on `EuclideanSpace ℝ (Fin n)` is countably generated, with
complements of closed balls of integer radii as a basis. -/
instance isCountablyGenerated_cocompact_euclidean :
    (Filter.cocompact (EuclideanSpace ℝ (Fin n))).IsCountablyGenerated := by
  have hbasis : (Filter.cocompact (EuclideanSpace ℝ (Fin n))).HasBasis
    (fun (_ : ℕ) => True) (fun r => (Metric.closedBall 0 (r : ℝ))ᶜ) := by
    constructor
    intro s
    simp only [true_and]
    constructor
    · intro hs
      rw [Filter.mem_cocompact] at hs
      obtain ⟨K, hK, hKs⟩ := hs
      obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
      refine ⟨⌈r⌉₊, fun x hx => hKs ?_⟩
      simp only [mem_compl_iff] at hx ⊢
      intro hxK
      have := hr hxK
      simp only [Metric.mem_closedBall, dist_zero_right] at this hx
      linarith [Nat.le_ceil r]
    · intro ⟨r, hrs⟩
      rw [Filter.mem_cocompact]
      exact ⟨Metric.closedBall 0 r, ProperSpace.isCompact_closedBall 0 r, hrs⟩
  exact hbasis.isCountablyGenerated

end ConvolutionDensity
end

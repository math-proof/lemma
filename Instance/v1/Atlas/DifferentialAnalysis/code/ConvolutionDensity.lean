/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConvolutionDensity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.DifferentialAnalysis.code.ConvolutionDensityFix
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.ConvolutionDensityFix
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.TestFunctions
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.SchwartzCutoffConvergence
public import Instance.v1.Atlas.DifferentialAnalysis.code.TestFunctions
public import Def.v1.Atlas.DifferentialAnalysis.code.SchwartzCutoffConvergence
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
@[expose] public section

open scoped ZeroAtInfty Convolution
open MeasureTheory Filter Topology Function Set TestFunctions


noncomputable section

namespace ConvolutionDensity

/-- The cocompact filter on Euclidean space is countably generated: it has a
countable basis given by complements of closed balls of integer radius. -/
instance cocompact_eucl_countablyGenerated {n : ℕ} :
    (Filter.cocompact (EuclideanSpace ℝ (Fin n))).IsCountablyGenerated := by
  apply Filter.HasCountableBasis.isCountablyGenerated (ι := ℕ)
    (p := fun _ => True)
    (s := fun m => (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) m)ᶜ)
  exact {
    countable := Set.countable_univ.mono (fun _ _ => trivial)
    toHasBasis := {
      mem_iff' := by
        intro S; simp only [true_and]
        constructor
        · intro hS
          rw [Filter.mem_cocompact] at hS
          obtain ⟨K, hK, hKS⟩ := hS
          obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
          obtain ⟨m, hm⟩ := exists_nat_ge r
          exact ⟨m, fun x hx => hKS fun hxK => by
            simp only [Set.mem_compl_iff, Metric.mem_closedBall, not_le] at hx
            exact absurd (le_trans (hr hxK) hm) (not_le.mpr hx)⟩
        · rintro ⟨m, hm⟩
          exact Filter.mem_cocompact.mpr
            ⟨Metric.closedBall 0 m, isCompact_closedBall 0 m, hm⟩
    }
  }

end ConvolutionDensity
end

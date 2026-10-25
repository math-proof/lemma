/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConvolutionDensity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.DifferentialAnalysis.code.ConvolutionDensityFix
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.ConvolutionDensityFix
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.TestFunctions
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SchwartzCutoffConvergence
import Instance.v1.Atlas.DifferentialAnalysis.code.TestFunctions
import Def.v1.Atlas.DifferentialAnalysis.code.SchwartzCutoffConvergence
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
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

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConvolutionSmooth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.DifferentialAnalysis.code.TestFunctions
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.TestFunctions
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Def.v1.Atlas.DifferentialAnalysis.code.ConvolutionSmooth
open scoped ZeroAtInfty Convolution SchwartzMap ContDiff
open MeasureTheory Filter Topology Function Set TestFunctions
open ContinuousLinearMap


noncomputable section

namespace ConvolutionSmooth

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 80000 in


/-- The cocompact filter on `EuclideanSpace ℝ (Fin d)` is countably generated, with a
basis of complements of closed balls of integer radii. -/
instance cocompact_isCountablyGenerated (d : ℕ) :
    (cocompact (EuclideanSpace ℝ (Fin d))).IsCountablyGenerated := by
  apply HasCountableBasis.isCountablyGenerated (ι := ℕ) (p := fun _ => True)
    (s := fun k => (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) k)ᶜ)
  exact ⟨⟨fun s => ⟨fun hs => by
    rw [mem_cocompact] at hs; obtain ⟨K, hK, hKs⟩ := hs
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    exact ⟨⌈R⌉₊, trivial, fun x hx => by
      apply hKs; intro hxK
      have h2 : (⌈R⌉₊ : ℝ) < dist x 0 := by
        rwa [Set.mem_compl_iff, Metric.mem_closedBall, not_le] at hx
      linarith [Nat.le_ceil R, Metric.mem_closedBall.mp (hR hxK)]⟩,
    fun ⟨k, _, hk⟩ => mem_cocompact.mpr ⟨_, isCompact_closedBall 0 k, hk⟩⟩⟩,
    countable_univ.to_subtype⟩


end ConvolutionSmooth
end

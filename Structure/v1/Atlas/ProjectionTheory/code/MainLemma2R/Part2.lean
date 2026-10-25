/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemma2R.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Def.v1.Atlas.ProjectionTheory.code.MainLemma2R.Part2


noncomputable section

open MeasureTheory Metric Set Finset

open scoped Classical InnerProductSpace

namespace ProjectionTheory

/-- A collection of $1 \times R$ tubes in $\mathbb{R}^2$ together with smooth bump
functions $\psi_i$ adapted to each tube and a (compactly supported) Fourier bound.
This is the data $f = \sum_T \psi_T$ used in the real-version Main Lemma 2R. -/
structure TubeCollection where
  R : ℝ
  hR : 1 ≤ R
  ι : Type
  [hι : Fintype ι]
  tubes : ι → Tube
  tubes_scale : ∀ i, (tubes i).R = R
  ψ : ι → (EuclideanSpace ℝ (Fin 2) → ℝ)
  ψ_smooth : ∀ i, ContDiff ℝ ⊤ (ψ i)
  ψ_integrable : ∀ i, Integrable (ψ i) volume
  fourierSupportBound : ℝ
  ψ_fourier_compact_support : ∀ i, ∀ ξ : EuclideanSpace ℝ (Fin 2),
    ‖ξ‖ > fourierSupportBound → fourierTransformR2 (ψ i) ξ = 0

end ProjectionTheory
end

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/Tightness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded

open MeasureTheory Set

namespace MeasureTheory.Measure

/-- A family of probability measures `μ : ι → Measure α` is **tight** if for every `ε > 0` there
exists a compact set `K` such that `μ i K ≥ 1 - ε` for every index `i`. -/
def IsTightFamily {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    {ι : Type*} (μ : ι → Measure α) [∀ i, IsProbabilityMeasure (μ i)] : Prop :=
  ∀ ε : ENNReal, 0 < ε → ∃ K : Set α, IsCompact K ∧ ∀ i, μ i K ≥ 1 - ε

/-- A family of probability measures on `ℝ` is **tight** if for every `ε > 0` there exists `M > 0`
such that `μ i [-M, M] ≥ 1 - ε` for every index `i`. This is the textbook definition specialised
to the real line. -/
def IsTightFamilyReal {ι : Type*} (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] : Prop :=
  ∀ ε : ENNReal, 0 < ε → ∃ M : ℝ, ∀ i, μ i (Set.Icc (-M) M) ≥ 1 - ε

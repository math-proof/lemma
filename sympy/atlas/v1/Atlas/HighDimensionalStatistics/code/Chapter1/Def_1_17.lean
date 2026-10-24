/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Def_1_17.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Cover

open Set Metric
open scoped NNReal

/-- **Definition 1.17 (ε-net).** A set `N ⊆ K` is an `ε`-net of `K` with
respect to the metric `d` if every point of `K` is within distance `ε` of some
point of `N`. -/
def IsEpsilonNet {α : Type*} [PseudoMetricSpace α] (K : Set α) (N : Set α) (ε : ℝ) : Prop :=
  N ⊆ K ∧ ∀ z ∈ K, ∃ x ∈ N, dist x z ≤ ε

namespace IsEpsilonNet

variable {α : Type*} [PseudoMetricSpace α] {K N : Set α} {ε : ℝ}

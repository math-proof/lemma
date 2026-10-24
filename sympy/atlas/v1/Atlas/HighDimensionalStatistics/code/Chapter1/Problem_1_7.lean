/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Problem_1_7.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter1.Def_1_17
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter1.Def_1_17
import Mathlib.Topology.MetricSpace.CoveringNumbers

open Set Metric
open scoped NNReal ENNReal

/-- A set `S ⊆ K` is `ε`-separated if any two distinct points of `S` are at
distance greater than `ε`. Used to define packing numbers. -/
def IsEpsilonSeparated {α : Type*} [PseudoMetricSpace α] (K S : Set α) (ε : ℝ) : Prop :=
  S ⊆ K ∧ S.Pairwise (fun z z' => dist z z' > ε)

namespace IsEpsilonSeparated

variable {α : Type*} [PseudoMetricSpace α] {K S : Set α} {ε : ℝ}

/-- The `ε`-covering number of `K`: the minimal size (possibly `∞`) of an
`ε`-net covering `K`. Wrapper around Mathlib's `Metric.coveringNumber`. -/
noncomputable def epsilonCoveringNumber {α : Type*} [PseudoEMetricSpace α]
    (ε : ℝ≥0) (K : Set α) : ℕ∞ :=
  Metric.coveringNumber ε K

/-- The `ε`-packing number of `K`: the maximal size of an `ε`-separated subset
of `K`. Wrapper around Mathlib's `Metric.packingNumber`. -/
noncomputable def epsilonPackingNumber {α : Type*} [PseudoEMetricSpace α]
    (ε : ℝ≥0) (K : Set α) : ℕ∞ :=
  Metric.packingNumber ε K

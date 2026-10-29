/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/MeasuresAndSigmaAlgebras.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.OuterMeasure.Caratheodory
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Content
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Basic
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.MetricSpace.Basic
open MeasureTheory Set

open scoped ENNReal


namespace MeasuresAndSigmaAlgebras

/-- Predicate axiomatising an outer measure `μ*` on `X`: empty set has measure zero,
monotone with respect to inclusion, and countably subadditive. -/
structure IsOuterMeasure {X : Type*} (μstar : Set X → ENNReal) : Prop where
  empty : μstar ∅ = 0
  mono : ∀ {A B : Set X}, A ⊆ B → μstar A ≤ μstar B
  iUnion_le : ∀ (A : ℕ → Set X), μstar (⋃ j, A j) ≤ ∑' j, μstar (A j)

end MeasuresAndSigmaAlgebras

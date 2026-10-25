/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/OuterMeasureFromFunctional.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.Content
import Mathlib.MeasureTheory.OuterMeasure.Induced
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Order
import Def.v1.Atlas.DifferentialAnalysis.code.MeasuresAndSigmaAlgebras.Part3
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.MeasuresAndSigmaAlgebras
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.ContinuousFunctions
import Def.v1.Atlas.DifferentialAnalysis.code.ContinuousFunctions.Part2
import Def.v1.Atlas.DifferentialAnalysis.code.OuterMeasureFromFunctional


noncomputable section

open Set TopologicalSpace MeasureTheory

open scoped ENNReal NNReal Topology ZeroAtInfty

namespace MeasuresAndSigmaAlgebras

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X]

/-- A continuous function vanishing at infinity whose topological support is contained in `∅`
must be identically zero. -/
theorem zeroAtInfty_eq_zero_of_tsupport_subset_empty
    {X : Type*} [MetricSpace X] {f : C₀(X, ℝ)}
    (h : tsupport f ⊆ (∅ : Set X)) : f = 0 := by
  ext x
  simp only [ZeroAtInftyContinuousMap.zero_apply]
  by_contra hne
  have hmem : x ∈ tsupport (⇑f : X → ℝ) := subset_closure hne
  exact (h hmem).elim

/-- The functional premeasure of the empty open set is zero: the only test function with
support in `∅` is the zero function. -/
theorem functionalMeasureOpen_empty
    {X : Type*} [MetricSpace X] (u : C₀(X, ℝ) →L[ℝ] ℝ) :
    functionalMeasureOpen u ∅ isOpen_empty = 0 := by
  simp only [functionalMeasureOpen]
  apply le_antisymm _ (zero_le _)
  apply iSup₂_le
  intro f ⟨_, _, hsupp⟩
  rw [zeroAtInfty_eq_zero_of_tsupport_subset_empty hsupp, map_zero, ENNReal.ofReal_zero]


end MeasuresAndSigmaAlgebras
end

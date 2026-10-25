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
import Instance.v1.Atlas.DifferentialAnalysis.code.MeasuresAndSigmaAlgebras.Part2
open MeasureTheory Set

open scoped ENNReal


section RieszMeasureFromC0

open Measure RealRMK

open scoped CompactlySupported ZeroAtInfty

variable {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] [LocallyCompactSpace X]

/-- Linear inclusion of compactly supported continuous functions into the space of
continuous functions vanishing at infinity. -/
noncomputable def inclusionCcC0 : C_c(X, ℝ) →ₗ[ℝ] C₀(X, ℝ) where
  toFun f := ⟨f.toContinuousMap, zero_at_infty f⟩
  map_add' f g := by
    apply ZeroAtInftyContinuousMap.ext; intro x
    simp only [ZeroAtInftyContinuousMap.coe_add, Pi.add_apply]
    rfl
  map_smul' r f := by
    apply ZeroAtInftyContinuousMap.ext; intro x
    simp only [ZeroAtInftyContinuousMap.coe_smul, Pi.smul_apply, RingHom.id_apply]
    rfl

/-- Restriction of a positive linear functional on `C₀(X, ℝ)` to `C_c(X, ℝ)`, viewed
as a positive linear map. -/
noncomputable def restrictC0ToCc
    (Φ : C₀(X, ℝ) →ₗ[ℝ] ℝ)
    (hΦ : ∀ f : C₀(X, ℝ), (∀ x, 0 ≤ f x) → 0 ≤ Φ f) :
    C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀ (Φ.comp inclusionCcC0) fun f hf => by
    apply hΦ; intro x; exact hf x

/-- The Riesz measure on `X` produced from a positive linear functional defined on
`C₀(X, ℝ)`, by restricting it to `C_c(X, ℝ)` and applying the RMK theorem. -/
noncomputable def rieszMeasureOfC0Functional
    (Φ : C₀(X, ℝ) →ₗ[ℝ] ℝ)
    (hΦ : ∀ f : C₀(X, ℝ), (∀ x, 0 ≤ f x) → 0 ≤ Φ f) :
    Measure X :=
  rieszMeasure (restrictC0ToCc Φ hΦ)

end RieszMeasureFromC0

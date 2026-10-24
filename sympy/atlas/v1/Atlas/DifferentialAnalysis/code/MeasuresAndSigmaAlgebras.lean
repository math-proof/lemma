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
structure IsOuterMeasure {X : Type*} (μstar : Set X → ℝ≥0∞) : Prop where
  empty : μstar ∅ = 0
  mono : ∀ {A B : Set X}, A ⊆ B → μstar A ≤ μstar B
  iUnion_le : ∀ (A : ℕ → Set X), μstar (⋃ j, A j) ≤ ∑' j, μstar (A j)

/-- Conversion from an `IsOuterMeasure` proof to a Mathlib `OuterMeasure` bundle. -/
noncomputable def IsOuterMeasure.toOuterMeasure {X : Type*} {μstar : Set X → ℝ≥0∞}
    (h : IsOuterMeasure μstar) : OuterMeasure X where
  measureOf := μstar
  empty := h.empty
  mono hsub := h.mono hsub
  iUnion_nat s _ := (h.iUnion_le s)

/-- Volume of the axis-aligned rectangle `[a, b]` in `ℝⁿ`, defined as the product of
side lengths `b i - a i`. -/
@[simp]
noncomputable def rectangleVolume {n : ℕ} (a b : Fin n → ℝ) : ℝ≥0∞ :=
  ∏ i, ENNReal.ofReal (b i - a i)


/-- The Lebesgue measure of a closed rectangle `[a, b]` in `ℝⁿ` equals the product of
its side lengths. -/
abbrev SigmaAlgebra (X : Type*) := MeasurableSpace X

section SigmaAlgebraAxioms

variable {X : Type*} [MeasurableSpace X]

end SigmaAlgebraAxioms

section RadonMeasure

open Measure

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

/-- A Radon measure on a topological measurable space is a Borel measure that is
regular (inner regular on opens, outer regular, locally finite). -/
class IsRadonMeasure (μ : Measure X) extends Regular μ : Prop

/-- Any regular measure is automatically a Radon measure in our sense. -/
instance Regular.toIsRadonMeasure (μ : Measure X) [Regular μ] : IsRadonMeasure μ := ⟨⟩

end RadonMeasure

/-- Carathéodory measurability condition: `E` splits every test set `A` additively
with respect to the outer measure `μ*`. -/
def IsOuterMeasureMeasurable {X : Type*} (μstar : Set X → ℝ≥0∞) (E : Set X) : Prop :=
  ∀ A : Set X, μstar A = μstar (A ∩ E) + μstar (A ∩ Eᶜ)

/-- The measure on the Carathéodory σ-algebra induced by an outer measure `μ` by
restriction. -/
noncomputable def caratheodoryMeasure : @Measure X μ.caratheodory :=
  letI : MeasurableSpace X := μ.caratheodory
  μ.toMeasure le_rfl

/-- The Riesz-Markov-Kakutani measure associated with a positive linear functional
on `C_c(X, ℝ)` is a Radon measure. -/
instance rieszMeasure_isRadonMeasure : IsRadonMeasure (rieszMeasure Λ) :=
  ⟨⟩

end RieszMeasureRadon

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

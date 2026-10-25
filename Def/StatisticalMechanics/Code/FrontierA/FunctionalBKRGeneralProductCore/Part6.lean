/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRFiniteCoordinateBlocks.Part6
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProductCore.Part5
open MeasureTheory Set
open Filter Topology
open scoped BigOperators ENNReal


namespace StatMech.FrontierA

universe u v

variable {E : Type u} [Fintype E] [DecidableEq E]
  {S : E → Type v} [∀ e, MeasurableSpace (S e)]


def PiDependsOn (K : Set E) (h : (∀ e, S e) → ℝ) : Prop :=
  ∀ ⦃x y⦄, piAgreeOn K x y → h x = h y


noncomputable def piFunctionalFamilyMax
    (F : Set E → (∀ e, S e) → ℝ) (x : ∀ e, S e) : ℝ :=
  (Finset.univ : Finset (Set E)).sup'
    (Finset.univ_nonempty : (Finset.univ : Finset (Set E)).Nonempty)
    fun K => F K x


noncomputable def piFunctionalFamilyDisjointMaxAt
    (F G : Set E → (∀ e, S e) → ℝ) (x y : ∀ e, S e) : ℝ :=
  (disjointCoordinatePairs E).sup' (disjointCoordinatePairs_nonempty (E := E))
    fun pair => F pair.1 x * G pair.2 y

noncomputable def piFunctionalFamilyDisjointMax
    (F G : Set E → (∀ e, S e) → ℝ) (x : ∀ e, S e) : ℝ :=
  piFunctionalFamilyDisjointMaxAt F G x x


def HasMeasurableFunctionalBKR (μ : ∀ e, Measure (S e)) : Prop :=
  ∀ (F G : Set E → (∀ e, S e) → ℝ),
    (∀ K, Measurable (F K)) → (∀ K, Measurable (G K)) →
    (∀ K x, 0 ≤ F K x) → (∀ K x, 0 ≤ G K x) →
    (∀ K, PiDependsOn K (F K)) → (∀ K, PiDependsOn K (G K)) →
    (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyDisjointMax F G x)
        ∂Measure.pi μ) ≤
      (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax F x) ∂Measure.pi μ) *
        ∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax G x) ∂Measure.pi μ


def HasMeasurableDualFunctionalBKR (μ : ∀ e, Measure (S e)) : Prop :=
  ∀ (F G : Set E → (∀ e, S e) → ℝ),
    (∀ K, Measurable (F K)) → (∀ K, Measurable (G K)) →
    (∀ K x, 0 ≤ F K x) → (∀ K x, 0 ≤ G K x) →
    (∀ K, PiDependsOn K (F K)) → (∀ K, PiDependsOn K (G K)) →
    (∫⁻ p, ENNReal.ofReal (piFunctionalFamilyDisjointMaxAt F G p.1 p.2)
        ∂(Measure.pi μ).prod (Measure.pi μ)) ≤
      ∫⁻ x, ENNReal.ofReal
        (piFunctionalFamilyMax F x * piFunctionalFamilyMax G x)
        ∂Measure.pi μ

end StatMech.FrontierA

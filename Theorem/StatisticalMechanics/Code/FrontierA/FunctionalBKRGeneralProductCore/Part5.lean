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
import Def.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProductCore.Part5
open MeasureTheory Set
open Filter Topology
open scoped BigOperators ENNReal


namespace StatMech.FrontierA

universe u v

variable {E : Type u} [Fintype E] [DecidableEq E]
  {S : E → Type v} [∀ e, MeasurableSpace (S e)]


theorem piFunctionalDisjointEssMaxAt_nonneg
    (μ : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (μ e)]
    (f g : (∀ e, S e) → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (x y : ∀ e, S e) :
    0 ≤ piFunctionalDisjointEssMaxAt μ f g x y := by
  unfold piFunctionalDisjointEssMaxAt
  let pair : Set E × Set E := (∅, ∅)
  have hpair : pair ∈ disjointCoordinatePairs E := by
    exact mem_disjointCoordinatePairs.mpr (Set.empty_disjoint ∅)
  calc
    0 ≤ piCylinderEssInf μ f pair.1 x *
        piCylinderEssInf μ g pair.2 y :=
      mul_nonneg (piCylinderEssInf_nonneg μ f hf0 pair.1 x)
        (piCylinderEssInf_nonneg μ g hg0 pair.2 y)
    _ ≤ (disjointCoordinatePairs E).sup'
        (disjointCoordinatePairs_nonempty (E := E))
        (fun p => piCylinderEssInf μ f p.1 x *
          piCylinderEssInf μ g p.2 y) :=
      Finset.le_sup'
        (fun p : Set E × Set E => piCylinderEssInf μ f p.1 x *
          piCylinderEssInf μ g p.2 y) hpair

theorem measurable_piFunctionalDisjointEssMaxAt
    (μ : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (μ e)]
    (f g : (∀ e, S e) → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    Measurable (fun p : (∀ e, S e) × (∀ e, S e) =>
      piFunctionalDisjointEssMaxAt μ f g p.1 p.2) := by
  have hrw : (fun p : (∀ e, S e) × (∀ e, S e) =>
      piFunctionalDisjointEssMaxAt μ f g p.1 p.2) =
      (disjointCoordinatePairs E).sup'
        (disjointCoordinatePairs_nonempty (E := E))
        (fun pair p => piCylinderEssInf μ f pair.1 p.1 *
          piCylinderEssInf μ g pair.2 p.2) := by
    funext p
    rw [piFunctionalDisjointEssMaxAt, Finset.sup'_apply]
  rw [hrw]
  apply Finset.measurable_sup'
  intro pair _
  exact ((measurable_piCylinderEssInf μ f hf hf0 pair.1).comp measurable_fst).mul
    ((measurable_piCylinderEssInf μ g hg hg0 pair.2).comp measurable_snd)

theorem measurable_piFunctionalDisjointEssMax
    (μ : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (μ e)]
    (f g : (∀ e, S e) → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    Measurable (piFunctionalDisjointEssMax μ f g) := by
  have hrw : piFunctionalDisjointEssMax μ f g =
      (disjointCoordinatePairs E).sup'
        (disjointCoordinatePairs_nonempty (E := E))
        (fun pair x => piCylinderEssInf μ f pair.1 x *
          piCylinderEssInf μ g pair.2 x) := by
    funext x
    rw [piFunctionalDisjointEssMax, piFunctionalDisjointEssMaxAt,
      Finset.sup'_apply]
  rw [hrw]
  apply Finset.measurable_sup'
  intro pair _
  exact (measurable_piCylinderEssInf μ f hf hf0 pair.1).mul
    (measurable_piCylinderEssInf μ g hg hg0 pair.2)


end StatMech.FrontierA

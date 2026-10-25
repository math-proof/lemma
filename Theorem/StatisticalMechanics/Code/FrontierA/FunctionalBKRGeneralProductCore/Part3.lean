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
import Def.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProductCore.Part3
open MeasureTheory Set
open Filter Topology
open scoped BigOperators ENNReal


namespace StatMech.FrontierA

universe u v

variable {E : Type u} [Fintype E] [DecidableEq E]
  {S : E → Type v} [∀ e, MeasurableSpace (S e)]


theorem piCylinderEssInf_eq_of_piAgreeOn
    (μ : ∀ e, Measure (S e)) (f : (∀ e, S e) → ℝ)
    (K : Set E) {x y : ∀ e, S e} (hxy : piAgreeOn K x y) :
    piCylinderEssInf μ f K x = piCylinderEssInf μ f K y := by
  have hassemble : piFiberAssemble K x = piFiberAssemble K y := by
    funext z e
    by_cases he : e ∈ K
    · simp [piFiberAssemble, he, hxy e he]
    · simp [piFiberAssemble, he]
  simp only [piCylinderEssInf, hassemble]


theorem piCylinderEssInf_nonneg
    (μ : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (μ e)]
    (f : (∀ e, S e) → ℝ) (hf0 : ∀ x, 0 ≤ f x)
    (K : Set E) (x : ∀ e, S e) :
    0 ≤ piCylinderEssInf μ f K x := by
  refine le_essInf_of_ae_le 0 (Filter.Eventually.of_forall fun z => ?_)
    (ae_isCoboundedUnder_ge_real
      (Measure.pi fun i : {e : E // e ∉ K} => μ i)
      (fun z => f (piFiberAssemble K x z)))
  exact hf0 _


end StatMech.FrontierA

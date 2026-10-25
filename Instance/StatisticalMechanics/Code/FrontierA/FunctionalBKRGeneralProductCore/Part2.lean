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
import Def.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProductCore.Part2
open MeasureTheory Set
open Filter Topology
open scoped BigOperators ENNReal


namespace StatMech.FrontierA

universe u v

variable {E : Type u} [Fintype E] [DecidableEq E]
  {S : E → Type v} [∀ e, MeasurableSpace (S e)]


instance piAgreementFiberMeasure.instIsProbabilityMeasure
    (μ : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (μ e)]
    (K : Set E) (x : ∀ e, S e) :
    IsProbabilityMeasure (piAgreementFiberMeasure μ K x) := by
  unfold piAgreementFiberMeasure
  exact inferInstance


end StatMech.FrontierA

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
import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProductCore.Part7
open MeasureTheory Set
open Filter Topology
open scoped BigOperators ENNReal


namespace StatMech.FrontierA

universe u v

variable {E : Type u} [Fintype E] [DecidableEq E]
  {S : E → Type v} [∀ e, MeasurableSpace (S e)]


section DependentBlocks

variable {D : E → Type*} [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)]
  [∀ e, Fintype (S e)]

def decodeDependentBlockConfig
    (decode : ∀ e, (D e → Bool) → S e)
    (omega : StatMech.ConfigSpace (Sigma D)) : ∀ e, S e :=
  fun e => decode e (fun d => omega ⟨e, d⟩)


def dependentWholeBlocks (K : Set E) : Set (Sigma D) :=
  {z | z.1 ∈ K}

end DependentBlocks
end StatMech.FrontierA

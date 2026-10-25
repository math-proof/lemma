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
import Instance.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProductCore
open MeasureTheory Set
open Filter Topology
open scoped BigOperators ENNReal


namespace StatMech.FrontierA

universe u v

variable {E : Type u} [Fintype E] [DecidableEq E]
  {S : E → Type v} [∀ e, MeasurableSpace (S e)]


noncomputable def piFiberSplit (K : Set E) :
    (∀ e, S e) ≃ᵐ
      ((∀ i : {e : E // e ∈ K}, S i) × PiFiberFreeConfig (S := S) K) := by
  classical
  exact MeasurableEquiv.piEquivPiSubtypeProd S (fun e => e ∈ K)


noncomputable def piFiberAssemble (K : Set E) (x : ∀ e, S e)
    (z : PiFiberFreeConfig (S := S) K) : ∀ e, S e := by
  classical
  intro e
  by_cases he : e ∈ K
  · exact x e
  · exact z ⟨e, he⟩

end StatMech.FrontierA

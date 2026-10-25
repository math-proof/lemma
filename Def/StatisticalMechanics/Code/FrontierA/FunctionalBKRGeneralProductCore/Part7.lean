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
import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProductCore.Part6
open MeasureTheory Set
open Filter Topology
open scoped BigOperators ENNReal


namespace StatMech.FrontierA

universe u v

variable {E : Type u} [Fintype E] [DecidableEq E]
  {S : E → Type v} [∀ e, MeasurableSpace (S e)]


def HasBernoulliBlockRepresentation {T : Type*} [Fintype T]
    (w : T → ℝ) : Prop :=
  ∃ (n : ℕ) (phi : Fin n → Bool → ℝ)
      (decode : (Fin n → Bool) → T),
    (∀ i b, 0 ≤ phi i b) ∧
    (∀ i, phi i false + phi i true = 1) ∧
    Function.Surjective decode ∧
    ∀ H : T → ℝ,
      productExpectation phi (H ∘ decode) = ∑ t, w t * H t

end StatMech.FrontierA

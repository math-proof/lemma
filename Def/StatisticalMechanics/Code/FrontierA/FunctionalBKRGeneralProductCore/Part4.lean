module
public import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRFiniteCoordinateBlocks.Part6
public import Mathlib.MeasureTheory.Function.EssSup
public import Mathlib.MeasureTheory.Function.SimpleFuncDense
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProductCore.Part3
open MeasureTheory Set
open Filter Topology
open scoped BigOperators ENNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

universe u v

variable {E : Type u} [Fintype E] [DecidableEq E]
  {S : E → Type v} [∀ e, MeasurableSpace (S e)]


noncomputable def piCylinderSublevelMeasure
    (μ : ∀ e, Measure (S e)) (f : (∀ e, S e) → ℝ)
    (K : Set E) (r : ℝ) (x : ∀ e, S e) : ENNReal :=
  Measure.pi (fun i : {e : E // e ∉ K} => μ i)
    {z | f (piFiberAssemble K x z) ≤ r}

end StatMech.FrontierA

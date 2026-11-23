/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/MeasuresAndSigmaAlgebras.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.OuterMeasure.Caratheodory
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Measure.Content
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Basic
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.Topology.MetricSpace.Basic
public import Instance.v1.Atlas.DifferentialAnalysis.code.MeasuresAndSigmaAlgebras

@[expose] public section

open MeasureTheory Set

open scoped ENNReal


namespace MeasuresAndSigmaAlgebras

/-- Carathéodory measurability condition: `E` splits every test set `A` additively
with respect to the outer measure `μ*`. -/
def IsOuterMeasureMeasurable {X : Type*} (μstar : Set X → ENNReal) (E : Set X) : Prop :=
  ∀ A : Set X, μstar A = μstar (A ∩ E) + μstar (A ∩ Eᶜ)

/-- The measure on the Carathéodory σ-algebra induced by an outer measure `μ` by
restriction. -/
noncomputable def caratheodoryMeasure : @Measure X μ.caratheodory :=
  letI : MeasurableSpace X := μ.caratheodory
  μ.toMeasure le_rfl

end MeasuresAndSigmaAlgebras

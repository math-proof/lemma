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
import Instance.v1.Atlas.DifferentialAnalysis.code.MeasuresAndSigmaAlgebras
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

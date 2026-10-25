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
import Abbrev.v1.Atlas.DifferentialAnalysis.code.MeasuresAndSigmaAlgebras
open MeasureTheory Set

open scoped ENNReal


namespace MeasuresAndSigmaAlgebras

section RadonMeasure

open Measure

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

/-- A Radon measure on a topological measurable space is a Borel measure that is
regular (inner regular on opens, outer regular, locally finite). -/
class IsRadonMeasure (μ : Measure X) extends Regular μ : Prop

end RadonMeasure
end MeasuresAndSigmaAlgebras

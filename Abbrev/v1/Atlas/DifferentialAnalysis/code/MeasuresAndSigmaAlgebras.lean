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
import Def.v1.Atlas.DifferentialAnalysis.code.MeasuresAndSigmaAlgebras
open MeasureTheory Set

open scoped ENNReal


namespace MeasuresAndSigmaAlgebras

/-- The Lebesgue measure of a closed rectangle `[a, b]` in `ℝⁿ` equals the product of
its side lengths. -/
abbrev SigmaAlgebra (X : Type*) := MeasurableSpace X

end MeasuresAndSigmaAlgebras

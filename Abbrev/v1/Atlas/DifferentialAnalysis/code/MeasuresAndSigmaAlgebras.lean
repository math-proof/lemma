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
public import Def.v1.Atlas.DifferentialAnalysis.code.MeasuresAndSigmaAlgebras
@[expose] public section

open MeasureTheory Set

open scoped ENNReal


namespace MeasuresAndSigmaAlgebras

/-- The Lebesgue measure of a closed rectangle `[a, b]` in `ℝⁿ` equals the product of
its side lengths. -/
abbrev SigmaAlgebra (X : Type*) := MeasurableSpace X

end MeasuresAndSigmaAlgebras

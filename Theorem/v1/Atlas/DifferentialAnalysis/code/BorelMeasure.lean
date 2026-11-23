/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/BorelMeasure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.OuterMeasure.Caratheodory
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Basic
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import Def.v1.Atlas.DifferentialAnalysis.code.MeasuresAndSigmaAlgebras.Part3
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.MeasuresAndSigmaAlgebras

@[expose] public section

open MeasureTheory Measure Set TopologicalSpace
open scoped CompactlySupported ZeroAtInfty


namespace MeasuresAndSigmaAlgebras

section RieszMeasureBorel

open RealRMK

variable {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] [LocallyCompactSpace X]

end RieszMeasureBorel
end MeasuresAndSigmaAlgebras

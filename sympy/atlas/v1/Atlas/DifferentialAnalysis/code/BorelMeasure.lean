/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/BorelMeasure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.OuterMeasure.Caratheodory
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Basic
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.MeasuresAndSigmaAlgebras
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.MeasuresAndSigmaAlgebras

open MeasureTheory Measure Set TopologicalSpace
open scoped CompactlySupported ZeroAtInfty

namespace MeasuresAndSigmaAlgebras

section RieszMeasureBorel

open RealRMK

variable {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] [LocallyCompactSpace X]

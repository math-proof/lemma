/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/HellySelection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Bases
import Mathlib.Topology.Order.Compact
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Rat.Denumerable
import Instance.v1.Atlas.TheoryOfProbability.code.HellySelection
open Filter Set Function
open scoped Topology


/-- Given any monotone function `f : ℝ → ℝ`, the right-limit `rightLim f` is monotone
and right-continuous, yielding a canonical `MonotoneRightContinuous`. -/
noncomputable def ofMonotone (f : ℝ → ℝ) (hf : Monotone f) :
    MonotoneRightContinuous where
  toFun := rightLim f
  mono' := hf.rightLim
  right_continuous' x := continuousWithinAt_rightLim_Ici (hf.tendsto_rightLim x)


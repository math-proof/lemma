/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/HellySelection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Order.LeftRightLim
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Order.Compact
public import Mathlib.Data.Real.Archimedean
public import Mathlib.Data.Rat.Denumerable
public section

open Filter Set Function
open scoped Topology


/-- A real function `F : ℝ → ℝ` is a (cumulative) distribution function if it is
monotone non-decreasing, right-continuous, tends to `0` at `-∞`, and tends to `1`
at `+∞`. These are exactly the distribution functions of probability measures on `ℝ`. -/
structure IsDistributionFunction (F : ℝ → ℝ) : Prop where
  mono : Monotone F
  right_continuous : ∀ x, ContinuousWithinAt F (Ici x) x
  tendsto_atBot : Tendsto F atBot (𝓝 0)
  tendsto_atTop : Tendsto F atTop (𝓝 1)

/-- A bundled monotone, right-continuous real function `ℝ → ℝ`. This is the natural
class of subsequential limits arising in Helly's selection theorem. -/
structure MonotoneRightContinuous where
  toFun : ℝ → ℝ
  mono' : Monotone toFun
  right_continuous' : ∀ x, ContinuousWithinAt toFun (Ici x) x


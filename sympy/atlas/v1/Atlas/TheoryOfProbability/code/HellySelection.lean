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

namespace MonotoneRightContinuous

/-- Coercion allowing a `MonotoneRightContinuous` to be applied as a function `ℝ → ℝ`. -/
instance instCoeFun : CoeFun MonotoneRightContinuous fun _ => ℝ → ℝ :=
  ⟨toFun⟩

end MonotoneRightContinuous

/-- Given any monotone function `f : ℝ → ℝ`, the right-limit `rightLim f` is monotone
and right-continuous, yielding a canonical `MonotoneRightContinuous`. -/
noncomputable def ofMonotone (f : ℝ → ℝ) (hf : Monotone f) :
    MonotoneRightContinuous where
  toFun := rightLim f
  mono' := hf.rightLim
  right_continuous' x := continuousWithinAt_rightLim_Ici (hf.tendsto_rightLim x)

end HellySelection

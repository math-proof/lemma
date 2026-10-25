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
import Structure.v1.Atlas.TheoryOfProbability.code.HellySelection
open Filter Set Function
open scoped Topology


namespace MonotoneRightContinuous

/-- Coercion allowing a `MonotoneRightContinuous` to be applied as a function `ℝ → ℝ`. -/
instance instCoeFun : CoeFun MonotoneRightContinuous fun _ => ℝ → ℝ :=
  ⟨toFun⟩

end MonotoneRightContinuous

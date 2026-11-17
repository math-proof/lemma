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
public import Structure.v1.Atlas.Probability.code.HellySelection

@[expose] public section

open Filter Set Function
open scoped Topology


namespace MonotoneRightContinuous

/-- Coercion allowing a `MonotoneRightContinuous` to be applied as a function `ℝ → ℝ`. -/
instance instCoeFun : CoeFun MonotoneRightContinuous fun _ => ℝ → ℝ :=
  ⟨toFun⟩

end MonotoneRightContinuous

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/TwoEnds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Abbrev.v1.Atlas.ProjectionTheory.code.TwoEnds

@[expose] public section

noncomputable section

open Classical Finset BigOperators

namespace TwoEnds

/-- The `δ`-tube around the unit-length segment `{c + t v : |t| ≤ 1/2}`:
the set of points within Euclidean distance `δ` of some point on that segment. -/
def deltaTube (c v : Point) (δ : ℝ) : Set Point :=
  { x | ∃ t : ℝ, |t| ≤ 1/2 ∧ ‖x - (c + t • v)‖ ≤ δ }

/-- `IsDeltaTube T δ` says that `T` is a `δ`-tube, i.e. it is of the form
`deltaTube c v δ` for some centre `c` and unit-length direction `v`. -/
def IsDeltaTube (T : Set Point) (δ : ℝ) : Prop :=
  ∃ (c v : Point), ‖v‖ = 1 ∧ T = deltaTube c v δ

end TwoEnds
end

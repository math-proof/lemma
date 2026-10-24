/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/ContinuousFunctions/Limits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.ClusterPt
import Mathlib.Topology.Separation.Hausdorff

open Filter Topology Set

namespace ContinuousFunctions

/-- `x` is a cluster point of `S` if every punctured neighborhood `(x - δ, x + δ) \ {x}`
of `x` meets `S`, i.e. for all `δ > 0` there exists `y ∈ S` with `y ≠ x` and
`|y - x| < δ`. -/
def IsClusterPoint (S : Set ℝ) (x : ℝ) : Prop :=
  ∀ δ > 0, ∃ y ∈ S, y ≠ x ∧ |y - x| < δ

/-- `f` converges to `L` at `c` along `S`, written informally `f(x) → L` as `x → c`,
if for every `ε > 0` there exists `δ > 0` such that for all `x ∈ S` with
`0 < |x - c| < δ` one has `|f x - L| < ε`. -/
def FunctionConvergesAt (f : ℝ → ℝ) (S : Set ℝ) (c L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ S, 0 < |x - c| → |x - c| < δ → |f x - L| < ε

/-- The right-hand limit `f(x) → L` as `x → c⁺` along `S`: for every `ε > 0`
there exists `δ > 0` such that for all `x ∈ S` with `c < x < c + δ` one has
`|f x - L| < ε`. -/
def RightLimit (f : ℝ → ℝ) (S : Set ℝ) (c L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ S, c < x → x < c + δ → |f x - L| < ε

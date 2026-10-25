/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/FunctionSequences/Basic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open Filter Topology


/-- `ConvergesPointwise f g S` states that the sequence of functions `f n` converges pointwise
to `g` on `S`: for every `x ∈ S`, the sequence `f n x` tends to `g x` as `n → ∞`. -/
def ConvergesPointwise (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (S : Set ℝ) : Prop :=
  ∀ x ∈ S, Tendsto (fun n => f n x) atTop (nhds (g x))


/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/FlowCutBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Structure.v1.Atlas.CombinatorialOptimization.code.Flow.FlowCutBound.Part2

@[expose] public section

open Finset BigOperators


namespace NetworkFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def cutCapacity (N : FlowNetwork V) (C : STCut N) : ℝ :=
  ∑ u ∈ C.S, ∑ v ∈ C.Sᶜ, N.cap u v

end NetworkFlow

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/FlowCutBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Def.v1.Atlas.CombinatorialOptimization.code.Flow.FlowCutBound
public section

open Finset BigOperators


namespace NetworkFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

structure STCut (N : FlowNetwork V) where
  S : Finset V
  s_mem : N.s ∈ S
  t_not_mem : N.t ∉ S

end NetworkFlow

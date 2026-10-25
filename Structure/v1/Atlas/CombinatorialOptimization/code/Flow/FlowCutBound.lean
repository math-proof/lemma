/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/FlowCutBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open Finset BigOperators


namespace NetworkFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

structure FlowNetwork (V : Type*) [Fintype V] [DecidableEq V] where
  cap : V → V → ℝ
  s : V
  t : V
  s_ne_t : s ≠ t
  cap_nonneg : ∀ u v, 0 ≤ cap u v

structure STFlow (N : FlowNetwork V) where
  f : V → V → ℝ
  flow_nonneg : ∀ u v, 0 ≤ f u v
  flow_cap : ∀ u v, f u v ≤ N.cap u v
  conservation : ∀ v, v ≠ N.s → v ≠ N.t →
    ∑ u : V, f u v = ∑ u : V, f v u

end NetworkFlow

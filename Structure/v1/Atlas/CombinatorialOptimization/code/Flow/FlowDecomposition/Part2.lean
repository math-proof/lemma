/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/FlowDecomposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.CombinatorialOptimization.code.Flow.FlowCutBound.Part2
import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.Flow.FlowCutBound
import Instance.v1.Atlas.CombinatorialOptimization.code.Flow.FlowDecomposition
open Finset BigOperators Classical


namespace NetworkFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

structure FlowDecomposition (N : FlowNetwork V) (fl : STFlow N) where
  f' : STFlow N
  same_value : flowValue N f' = flowValue N fl
  support_sub : flowSupport N f' ⊆ flowSupport N fl
  k : ℕ
  paths : Fin k → FlowPath N
  weights : Fin k → ℝ
  weights_pos : ∀ i, 0 < weights i
  flow_eq : ∀ u v, f'.f u v =
    ∑ i : Fin k, if (paths i).mem_edges u v then weights i else 0
  k_le_support : k ≤ (flowSupport N fl).card

end NetworkFlow

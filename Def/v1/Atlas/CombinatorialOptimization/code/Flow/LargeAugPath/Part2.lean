/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/LargeAugPath.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.CombinatorialOptimization.code.Flow.FlowDecomposition.Part3
import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.Flow.FlowDecomposition
import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.Flow.ResidualGraph
import Def.v1.Atlas.CombinatorialOptimization.code.Flow.ResidualGraph.Part2
import Theorem.v1.Atlas.CombinatorialOptimization.code.Flow.LargeAugPath
open Finset BigOperators Classical


namespace NetworkFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def residualNetwork (N : FlowNetwork V) (fl : STFlow N) : FlowNetwork V :=
  { s := N.s
    t := N.t
    s_ne_t := N.s_ne_t
    cap := fun u v => resCap N fl u v
    cap_nonneg := fun u v => resCap_nonneg N fl u v }

noncomputable def diffFlowFun (N : FlowNetwork V) (fl fl_max : STFlow N) (u v : V) : ℝ :=
  max (fl_max.f u v - fl.f u v) 0 + max (fl.f v u - fl_max.f v u) 0

end NetworkFlow

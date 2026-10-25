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
import Theorem.v1.Atlas.CombinatorialOptimization.code.Flow.LargeAugPath.Part2
open Finset BigOperators Classical


namespace NetworkFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def diffFlow (N : FlowNetwork V) (fl fl_max : STFlow N) :
    STFlow (residualNetwork N fl) :=
  { f := diffFlowFun N fl fl_max
    flow_nonneg := diffFlowFun_nonneg N fl fl_max
    flow_cap := diffFlowFun_le_resCap N fl fl_max
    conservation := diffFlowFun_conservation N fl fl_max }

end NetworkFlow

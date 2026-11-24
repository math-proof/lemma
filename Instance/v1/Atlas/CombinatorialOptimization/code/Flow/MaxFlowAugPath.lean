module
public import Def.v1.Atlas.CombinatorialOptimization.code.Flow.MaxFlowMinCut.Part2
public import Theorem.Finset.Atlas.v1.CombinatorialOptimization.code.Flow.MaxFlowMinCut
public import Theorem.Finset.Atlas.v1.CombinatorialOptimization.code.Flow.LargeAugPath
public import Def.v1.Atlas.CombinatorialOptimization.code.Flow.LargeAugPath.Part3
public import Def.v1.Atlas.CombinatorialOptimization.code.Flow.MaxFlowAugPath
open Finset BigOperators Classical


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/MaxFlowAugPath.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

namespace NetworkFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

instance (l : List V) (u v : V) : Decidable (IsPathEdge l u v) :=
  Fintype.decidableExistsFintype

end NetworkFlow
end

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/MaxFlowAugPath.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.CombinatorialOptimization.code.Flow.MaxFlowMinCut.Part2
import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.Flow.MaxFlowMinCut
import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.Flow.LargeAugPath
import Def.v1.Atlas.CombinatorialOptimization.code.Flow.LargeAugPath.Part3
import Def.v1.Atlas.CombinatorialOptimization.code.Flow.MaxFlowAugPath
open Finset BigOperators Classical


noncomputable section

namespace NetworkFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

instance (l : List V) (u v : V) : Decidable (IsPathEdge l u v) :=
  Fintype.decidableExistsFintype

end NetworkFlow
end

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
open Finset BigOperators Classical


namespace NetworkFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

def IsMaxFlow (N : FlowNetwork V) (fl : STFlow N) : Prop :=
  ∀ fl' : STFlow N, flowValue N fl' ≤ flowValue N fl

noncomputable def edgeCount (N : FlowNetwork V) : ℕ :=
  (Finset.univ.filter (fun e : V × V => N.cap e.1 e.2 > 0)).card

end NetworkFlow

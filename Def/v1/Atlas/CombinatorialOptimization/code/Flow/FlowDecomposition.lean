/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/FlowDecomposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.CombinatorialOptimization.code.Flow.FlowCutBound.Part2
import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.Flow.FlowCutBound
open Finset BigOperators Classical


namespace NetworkFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def flowSupport (N : FlowNetwork V) (fl : STFlow N) : Finset (V × V) :=
  Finset.univ.filter (fun e => fl.f e.1 e.2 > 0)

end NetworkFlow

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/FlowDecomposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.CombinatorialOptimization.code.Flow.FlowCutBound.Part2
import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.Flow.FlowCutBound
import Structure.v1.Atlas.CombinatorialOptimization.code.Flow.FlowDecomposition.Part2
open Finset BigOperators Classical


namespace NetworkFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

def reachableInSupport (N : FlowNetwork V) (fl : STFlow N) (u v : V) : Prop :=
  Relation.ReflTransGen (fun a b => fl.f a b > 0) u v

noncomputable def reachableSet (N : FlowNetwork V) (fl : STFlow N) : Finset V :=
  Finset.univ.filter (fun v => reachableInSupport N fl N.s v)

end NetworkFlow

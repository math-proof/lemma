/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/FlowDecomposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.CombinatorialOptimization.code.Flow.FlowCutBound.Part2
import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.Flow.FlowCutBound
import Structure.v1.Atlas.CombinatorialOptimization.code.Flow.FlowDecomposition
open Finset BigOperators Classical


namespace NetworkFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

def FlowPath.edges {N : FlowNetwork V} (p : FlowPath N) : List (V × V) :=
  p.vertices.zip p.vertices.tail

def FlowPath.mem_edges {N : FlowNetwork V} (p : FlowPath N) (u v : V) : Prop :=
  (u, v) ∈ p.edges

end NetworkFlow

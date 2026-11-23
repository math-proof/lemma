/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/EdmondsRuntime.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.CombinatorialOptimization.code.Matching.EdmondsProgress
public import Theorem.Finset.Atlas.v1.CombinatorialOptimization.code.Matching.EdmondsProgress
public import Structure.v1.Atlas.CombinatorialOptimization.code.Matching.EdmondsRuntime

@[expose] public section

open SimpleGraph


namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable def sym2Endpoints (e : Sym2 V) : Finset V :=
  e.toMultiset.toFinset

end SimpleGraph

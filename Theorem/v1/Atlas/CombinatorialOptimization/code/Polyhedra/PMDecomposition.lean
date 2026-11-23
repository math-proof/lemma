/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Polyhedra/PMDecomposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Def.v1.Atlas.CombinatorialOptimization.code.Polyhedra.EdmondsPolytope
public import Theorem.Finset.Atlas.v1.CombinatorialOptimization.code.Polyhedra.EdmondsPolytope
open SimpleGraph Finset BigOperators Classical

public section

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

end SimpleGraph

noncomputable section

end

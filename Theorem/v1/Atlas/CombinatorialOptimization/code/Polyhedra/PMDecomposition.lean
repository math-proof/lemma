/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Polyhedra/PMDecomposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.CombinatorialOptimization.code.Polyhedra.EdmondsPolytope
import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.Polyhedra.EdmondsPolytope
open SimpleGraph Finset BigOperators Classical


namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

end SimpleGraph

noncomputable section

end

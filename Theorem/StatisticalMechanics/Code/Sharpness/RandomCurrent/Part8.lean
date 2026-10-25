/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/RandomCurrent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part6
open SimpleGraph Finset

set_option linter.unusedSectionVars false


namespace StatMech

namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem backbone_le (n : Current V) (x y : V)
    [LinearOrder (IsBackbonePath G n x y)]
    (h : Nonempty (IsBackbonePath G n x y)) (p : IsBackbonePath G n x y) :
    backbone G n x y h ≤ p :=
  Finset.min'_le _ _ (Finset.mem_univ p)


theorem IsBackbonePath.currentConnected {n : Current V} {x y : V}
    (p : IsBackbonePath G n x y) : CurrentConnected G n x y :=
  (p.1.mapLe (oddSubgraph_le_currentSubgraph G n)).reachable


end Sharpness
end StatMech

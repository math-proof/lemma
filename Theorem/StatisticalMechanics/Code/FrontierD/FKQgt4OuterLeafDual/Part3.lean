/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4OuterLeafDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
import Def.StatisticalMechanics.Code.FrontierD.FKQgt4OuterLeafDual.Part4
open Finset Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising

noncomputable section

theorem pfdOuterLeafEnds_collapse (P : PlanarZ2Subgraph)
    (e : kwg_Edge P) :
    Sym2.map (pfdOuterLeafCollapse P) (pfdOuterLeafEnds P e) =
      kwg_dualEnds P e := by
  simp only [pfdOuterLeafEnds, Sym2.map_pair_eq, pfdOuterLeafCollapse_endpoint,
    pfdOuterLeafSideFace, Bool.false_eq_true, if_false, if_true, kwg_dualEnds]


end
end StatMech.FrontierD

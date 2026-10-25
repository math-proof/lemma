/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4OuterLeafDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
import Def.StatisticalMechanics.Code.FrontierD.FKQgt4OuterLeafDual
open Finset Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising

noncomputable section

theorem pfdOuterFace_infinite (P : PlanarZ2Subgraph) :
    (pfdOuterFace P).supp.Infinite :=
  (kwg_unique_outerFace P).choose_spec.1

theorem pfdFace_eq_outer_of_infinite (P : PlanarZ2Subgraph)
    {C : kwg_Face P} (hC : C.supp.Infinite) :
    C = pfdOuterFace P :=
  (kwg_unique_outerFace P).choose_spec.2 C hC


end
end StatMech.FrontierD

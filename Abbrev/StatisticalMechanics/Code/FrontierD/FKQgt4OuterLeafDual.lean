/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4OuterLeafDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4OuterLeafDual
open Finset Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising

noncomputable section

abbrev pfdOuterLeafVertex (P : PlanarZ2Subgraph) :=
  {C : kwg_Face P // C ≠ pfdOuterFace P} ⊕
    (Unit ⊕ (kwg_Edge P × Bool))

end
end StatMech.FrontierD

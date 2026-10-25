/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4OuterLeafDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4OuterLeafDual.Part5
open Finset Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising

noncomputable section

def pfdOuterLeafClosedEdges (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) :
    Set (kwg_Edge P) :=
  {e | e.1 ∉ K.edgeSet}


def pfdOuterLeafLift (P : PlanarZ2Subgraph) (C : kwg_Face P) :
    pfdOuterLeafVertex P :=
  if h : C = pfdOuterFace P then Sum.inr (Sum.inl ())
  else Sum.inl ⟨C, h⟩

end
end StatMech.FrontierD

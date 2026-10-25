/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualLumpedLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareDualBundles.Part2
import Theorem.StatisticalMechanics.Code.FK.IndexedEdgeLumping.Part2
import Theorem.StatisticalMechanics.Code.FK.Tilt.Part3
import Instance.StatisticalMechanics.Code.FrontierD.FKQgt4SquareDualLumpedLaw
open Finset Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising StatMech.FK

noncomputable section

def pfdIndexedSupportActive (P : PlanarZ2Subgraph)
    (eta : ConfigSpace P.G.edgeSet) :
    ConfigSpace (pfdClosedDual P ⊥).edgeSet :=
  restrictActive (pfdClosedDual P ⊥)
    (indexedBundleSupport (kwg_dualEnds P) eta)


def pfdEdgeComplement (P : PlanarZ2Subgraph) :
    ConfigSpace P.G.edgeSet ≃ ConfigSpace P.G.edgeSet where
  toFun omega e := !(omega e)
  invFun omega e := !(omega e)
  left_inv := by intro omega; funext e; simp
  right_inv := by intro omega; funext e; simp

end
end StatMech.FrontierD

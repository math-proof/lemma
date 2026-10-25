/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredSweep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKGlobalSweep.Part5
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part18
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Structure.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredSweep
open Finset


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

noncomputable section

def TriHexFiniteWiredLevel.triangleBoundaryReachRatio
    (D : TriHexFiniteWiredLevel) (q p : Real) : Real := by
  letI := D.cellFintype
  letI := D.cellDecidableEq
  letI := D.vertexFintype
  letI := D.vertexDecidableEq
  letI := D.boundaryDecidable
  exact triangleFKFiniteWiredBoundaryReachRatio q
    (FrontierA.fkEdgeOdds p) (FrontierA.fkEdgeOdds p)
    (FrontierA.fkEdgeOdds p) D.terminal D.boundary D.root


def TriHexFiniteWiredLevel.starBoundaryReachRatio
    (D : TriHexFiniteWiredLevel) (q p : Real) : Real := by
  letI := D.cellFintype
  letI := D.cellDecidableEq
  letI := D.vertexFintype
  letI := D.vertexDecidableEq
  letI := D.boundaryDecidable
  let pStar := BeffaraDC.dualParam p q
  exact starFKFiniteWiredBoundaryReachRatio q
    (FrontierA.fkEdgeOdds pStar) (FrontierA.fkEdgeOdds pStar)
    (FrontierA.fkEdgeOdds pStar) D.terminal D.boundary D.root


end
end StatMech.FK.PeriodicPlanar

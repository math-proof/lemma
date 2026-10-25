/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceJordan.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourFinal.Part4
import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
import Theorem.StatisticalMechanics.Code.Walls.fwrfaceregion.Part3
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part11
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_centralFace_anchoredContactChoice_of_faithful_failure
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    RlcCentralFaceFilledBoundaryAnchoredContactChoice gamma gamma' rho := by
  obtain ⟨B, x, y, hx, hy, hxPath, hyPath, _hanchor, _hedges⟩ :=
    rlc_centralFace_retainedAnchorContactWalk_of_faithful_failure
      gamma gamma' hfaith rho hno
  have hbase : B.firstFace ∈ B.contour.support :=
    B.contour.fst_mem_support_of_mem_edges B.anchor_mem
  exact ⟨B, x, y, hx, hy, hxPath, hyPath,
    rlc_contourContactArcs_support_cover B.contour hx hy hbase⟩


end
end StatMech.Universality

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutSquareEmbedding.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterGraphBridge.Part10
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquarePeriodicDualCoordinates
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCriticalDualQuasiInvariant.Part2
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusSquareCrossingCover.Part7
import Def.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquare
open StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectSquareSiteVertex_siteOfPair
    (R : FKRectTorus) (p : Int × Int) :
    fkRectSquareSiteVertex R (fkRectSquareSiteOfPair p) =
      fkRectSquareRepresentativeVertex R p := by
  rfl


theorem fkRectDevelopedSquare_sharedPrimalEdge
    (n : Nat) {f g : Site 2}
    (hfg : (hypercubicLattice 2).Adj f g) :
    sharedPrimalEdge (fkRectDevelopedSquareSite n f)
        (fkRectDevelopedSquareSite n g) =
      Sym2.map (fkRectDevelopedSquareSite n) (sharedPrimalEdge f g) := by
  let t : Site 2 := ![2 * (n : Int), (n : Int)]
  simpa [fkRectDevelopedSquareSite, fkRectDevelopedSquarePoint,
    fkRectSquareSiteOfPair, t,
    StatMech.FK.PeriodicPlanar.siteTranslate] using
      (sharedPrimalEdge_add t f g)


end
end StatMech.FrontierD

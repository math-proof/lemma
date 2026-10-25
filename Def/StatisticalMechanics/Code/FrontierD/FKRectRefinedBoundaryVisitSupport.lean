/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryVisitSupport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedTranslatedLocalSupport
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryPermutation.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedBoundaryVisitSupport
open Finset


namespace StatMech.FrontierD

noncomputable section

def fkRectRefinedBoundaryMatchedVisitTrace
    (R : FKRectTorus) (pairing : FKMedialLoopPairing R.medialTorus)
    (e : R.EdgeIndex) :
    FKMedialDart R.medialTorus -> (Int × Int) -> Nat -> Int
  | _, _, 0 => 0
  | d, c, n + 1 =>
      (if fkRectTorusMedialEdgeEquiv R d.1 = e ∧
          let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
          (((c.1 : Int) : ZMod L), ((c.2 : Int) : ZMod L)) =
            ((((fkRectRefinedPrimalEdgeCenter R e).1 : Int) : ZMod L),
              (((fkRectRefinedPrimalEdgeCenter R e).2 : Int) : ZMod L))
        then if d = fkMedialWestDart (fkRectMedialVertexOfEdge R e)
          then 1 else -1
        else 0) +
      fkRectRefinedBoundaryMatchedVisitTrace R pairing e
        (fkMedialBoundaryStep pairing d)
        (fkRectRefinedBondCenter c (fkMedialLocalMate pairing d).2) n


end
end StatMech.FrontierD

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedOrbitInteraction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedInteractionCore.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryOrbitVisits.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedOrbitInteraction
open scoped BigOperators
open Equiv Finset


namespace StatMech.FrontierD

noncomputable section

def fkRectRefinedBoundaryLocalInteraction
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialDart R.medialTorus) (c : Int × Int)
    (e : R.EdgeIndex) : Int :=
  let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R)
  fkRectRefinedRawInteraction
    ((fkRectRefinedLocalDarts (pairing d.1) c d.2).map
      (fkRectIntegralSquareDartMod L))
    ((fkRectRefinedPrimalEdgeDarts R e).map
      (fkRectIntegralSquareDartMod L))


def fkRectRefinedBoundaryInteractionTrace
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (e : R.EdgeIndex) :
    FKMedialDart R.medialTorus -> (Int × Int) -> Nat -> Int
  | _, _, 0 => 0
  | d, c, n + 1 =>
      fkRectRefinedBoundaryLocalInteraction R pairing d c e +
        fkRectRefinedBoundaryInteractionTrace R pairing e
          (fkMedialBoundaryStep pairing d)
          (fkRectRefinedBondCenter c (fkMedialLocalMate pairing d).2) n


def FKRectRefinedBoundaryHasLocalVisitInteraction
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (e : R.EdgeIndex) (a b : FKMedialDart R.medialTorus) :
    FKMedialDart R.medialTorus -> (Int × Int) -> Nat -> Prop
  | _, _, 0 => True
  | d, c, n + 1 =>
      fkRectRefinedBoundaryLocalInteraction R pairing d c e =
          (if d = a then 1 else 0) - (if d = b then 1 else 0) ∧
        FKRectRefinedBoundaryHasLocalVisitInteraction R pairing e a b
          (fkMedialBoundaryStep pairing d)
          (fkRectRefinedBondCenter c (fkMedialLocalMate pairing d).2) n


end
end StatMech.FrontierD

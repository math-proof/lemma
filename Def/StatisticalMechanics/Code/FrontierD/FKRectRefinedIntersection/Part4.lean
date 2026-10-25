/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedInteractionCore.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedIntersection.Part4
open scoped BigOperators
open Finset


namespace StatMech.FrontierD

open StatMech.Onsager

open IntegralSquareTorusCycle

noncomputable section

variable {L : Nat} [Fact (8 < L)]

def fkRectRefinedBoundaryCanonicalCenter
    (R : FKRectTorus) (d : FKMedialDart R.medialTorus) : Int × Int :=
  fkRectRefinedPrimalEdgeCenter R
    (fkRectTorusMedialEdgeEquiv R d.1)


def fkRectMedialBoundaryPrimalSeamIncrement
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialDart R.medialTorus) : Int × Int :=
  let a := fkRectMedialDartPrimalLabel R d
  let b := fkRectMedialDartPrimalLabel R
    (fkMedialBoundaryStep pairing d)
  (fkRectHorizontalSeamIncrement R a b,
    fkRectVerticalSeamIncrement R a b)


def fkRectRefinedBoundaryPrimalLift
    (R : FKRectTorus) (d : FKMedialDart R.medialTorus) : Int × Int :=
  let e := fkRectTorusMedialEdgeEquiv R d.1
  let ends := fkRectLiftedIndexedEdgeEnds R e
  match fkRectClosedPairingAtEdge e, d.2 with
  | true, .east | true, .north | false, .west | false, .north => ends.1
  | true, .west | true, .south | false, .east | false, .south => ends.2


def fkRectRefinedBoundaryPrimalPotential
    (R : FKRectTorus) (d : FKMedialDart R.medialTorus) : Int × Int :=
  let z := fkRectSquareDevelopPoint (fkRectRefinedBoundaryPrimalLift R d)
  let a := fkRectVertexSquarePoint R (fkRectMedialDartPrimalLabel R d)
  (4 * (z.1 - a.1), 4 * (z.2 - a.2))

end
end StatMech.FrontierD

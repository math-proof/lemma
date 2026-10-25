/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialPrimalLabel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialToggleCount
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialPrimalLabel.Part2


namespace StatMech.FrontierD

def fkRectMedialDartPrimalLabel (R : FKRectTorus)
    (d : FKMedialDart R.medialTorus) : R.Vertex :=
  let e := fkRectTorusMedialEdgeEquiv R d.1
  match d.2 with
  | .west => fkRectMedialWestPrimal R e
  | .east => fkRectMedialEastPrimal R e
  | .south =>
      if fkRectClosedPairingAtEdge e then
        fkRectMedialWestPrimal R e
      else fkRectMedialEastPrimal R e
  | .north =>
      if fkRectClosedPairingAtEdge e then
        fkRectMedialEastPrimal R e
      else fkRectMedialWestPrimal R e


def fkRectClosedMedialPairing (R : FKRectTorus) :
    FKMedialLoopPairing R.medialTorus :=
  fun v => fkRectClosedPairingAtEdge (fkRectTorusMedialEdgeEquiv R v)


end StatMech.FrontierD

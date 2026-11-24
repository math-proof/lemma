module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part10
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBlockRepetition.Part11
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

def sixVertexHalfFilledStraightRectangle (N M : ℕ) :
    SixVertexRectangleArrows N M where
  horizontal _ := false
  vertical ik := sixVertexHalfFilledRow N ik.1


def sixVertexHalfFilledStraightBoundary (N M : ℕ) :
    SixVertexToroidalBoundary N M :=
  (fun _ => false, sixVertexHalfFilledRow N)

end StatMech.FrontierD

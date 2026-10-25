/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part10
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexBlockRepetition
open Finset


namespace StatMech.FrontierD

def sixVertexRectangleTileBlocks {N M a b : ℕ}
    {ξ : SixVertexToroidalBoundary N M}
    (ω : SixVertexRectangleBlockCopies ξ a b) :
    SixVertexRectangleArrows ((a + 1) * N) ((b + 1) * M) where
  horizontal kj :=
    let byj := finProdFinEquiv.symm kj.2
    Fin.lastCases
      ((ω (Fin.last a, byj.1)).1.horizontal (Fin.last N, byj.2))
      (fun gi =>
        let bxi := finProdFinEquiv.symm gi
        (ω (bxi.1, byj.1)).1.horizontal (bxi.2.castSucc, byj.2))
      kj.1
  vertical ik :=
    let bxi := finProdFinEquiv.symm ik.1
    Fin.lastCases
      ((ω (bxi.1, Fin.last b)).1.vertical (bxi.2, Fin.last M))
      (fun gj =>
        let byj := finProdFinEquiv.symm gj
        (ω (bxi.1, byj.1)).1.vertical (bxi.2, byj.2.castSucc))
      ik.2

end StatMech.FrontierD

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedBoundaryGluing
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFiniteTorus.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexParticleHole.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part6
open Finset Matrix


namespace StatMech.FrontierD

theorem svHorizontalOfBool_ice {N : Nat} (hN : 0 < N)
    (x y : SixVertexRow N) (hcount : sixVertexUpCount x = sixVertexUpCount y)
    (b : Bool)
    (hb : if b then svRowPrefixForward y x else svRowPrefixForward x y) :
    svHorizontalIce hN x y (svHorizontalOfBool x y b) := by
  cases b with
  | false =>
      exact svForwardHorizontal_ice hN x y hcount (by simpa using hb)
  | true =>
      exact svBackwardHorizontal_ice hN x y hcount (by simpa using hb)

end StatMech.FrontierD

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallisCore.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallisBridge


namespace StatMech.FrontierD

open Filter Topology Finset

noncomputable section

def sixVertexCanonicalOddActualHalfProduct
    {c : Real} (hc : 2 < c) (s k : Nat) : Real :=
  ∏ j : Fin (s + k + 1),
    ‖sixVertexBetheM c (sixVertexBethePhase
        (sixVertexCanonicalOddMidpointHalfRoot hc s k j))‖ /
      ‖sixVertexBetheM c (sixVertexBethePhase
        (sixVertexCanonicalOddLeftHalfRoot hc s k j))‖

end
end StatMech.FrontierD

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallisCore.Part2


namespace StatMech.FrontierD

open Filter Topology Finset

noncomputable section

theorem tendsto_sixVertexOddWallisReferenceProduct_bridge (s : Nat) :
    Tendsto (fun k =>
      (sixVertexFourWidth (2 * s + 1) k : Real) *
        sixVertexOddWallisHalfProduct (s + k + 1) ^ 2)
      atTop (nhds (4 / Real.pi)) :=
  tendsto_sixVertexOddWallisReferenceProduct s

end
end StatMech.FrontierD

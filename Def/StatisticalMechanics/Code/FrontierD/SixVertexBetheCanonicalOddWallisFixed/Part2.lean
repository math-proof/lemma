/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisFixed.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallis.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallisFixed.Part2


namespace StatMech.FrontierD

open Filter Topology Finset MeasureTheory

noncomputable section

def sixVertexCanonicalOddHalfPartitionRoot
    {c : Real} (hc : 2 < c) (s k j : Nat) : Real :=
  if hj : j < s + k + 2 then
    sixVertexCanonicalDensityPerronPositiveHalfRoots hc (2 * s + 1 + k)
      ⟨j, by omega⟩
  else 0

end
end StatMech.FrontierD

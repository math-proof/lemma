/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnalyticContinuation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPerronAnalytic.Part2
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexHalfFilledPerronNormalized (k : Nat) (c : Real) : Real :=
  sixVertexSectorTopEigenvalue (sixVertexFourWidth 0 k)
      ((k + 1) + (k + 1)) (by
        unfold sixVertexFourWidth
        omega) c /
    (c ^ 2 - 2) ^ ((k + 1) + (k + 1))


end
end StatMech.FrontierD

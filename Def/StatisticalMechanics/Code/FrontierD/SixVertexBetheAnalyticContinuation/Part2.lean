/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnalyticContinuation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPerronAnalytic.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnalyticContinuation
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexHalfFilledCandidateKernelAt (k : Nat) (c : Real) : Real :=
  (2 * ∏ j : Fin (k + 1),
    (((c ^ 2 - 1) ^ 2 + 1 + 2 * (c ^ 2 - 1) *
        Real.cos (sixVertexHalfFilledBetheRootAt k
          (Fin.natAdd (k + 1) j) c)) /
      (2 - 2 * Real.cos (sixVertexHalfFilledBetheRootAt k
        (Fin.natAdd (k + 1) j) c)))) /
    (c ^ 2 - 2) ^ ((k + 1) + (k + 1))

end
end StatMech.FrontierD

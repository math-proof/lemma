/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSpectralIsolation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPerronSpectralIsolation
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheRootBounds.Part2
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexHalfFilledBetheCandidateNormalized (k : Nat) (c : Real) : Real :=
  if hc : 2 < c then
    sixVertexSymmetricBetheEigenvalueValue c
        (sixVertexPositiveHalfBetheRoots hc k) /
      (c ^ 2 - 2) ^ ((k + 1) + (k + 1))
  else 0


end
end StatMech.FrontierD

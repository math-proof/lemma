/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEventualPerronBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheInfiniteAnisotropyGauge
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnalyticCandidateSheet.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEventualPerronBranch.Part4
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexCanonicalPerronCandidateRate
    {c : Real} (hc : 2 < c) (k : Nat) : Real :=
  Real.log (sixVertexSymmetricBetheEigenvalueValue c
      (sixVertexCanonicalPerronPositiveHalfRoots hc k)) /
    (sixVertexFourWidth 0 k : Real)

end
end StatMech.FrontierD

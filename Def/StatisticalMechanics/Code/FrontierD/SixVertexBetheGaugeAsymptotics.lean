/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheGaugeAsymptotics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnalyticCandidateSheet.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheGaugeAsymptotics
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexDensityGaugeOuterRadius (c rhoLower : Real) : Real :=
  rhoLower * ((sixVertexAnisotropyMagnitude c - 1) /
    sixVertexRootDensityScale c) / 4


def sixVertexDensityGaugeInnerRadius (c rhoLower : Real) : Real :=
  ((sixVertexRootDensityContractionRate c + 1) / 2) *
    sixVertexDensityGaugeOuterRadius c rhoLower

end
end StatMech.FrontierD

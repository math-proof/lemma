module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleFibre.Part13
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleMatching.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleMatching.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByFourAuditedCoordinateParameterImage :
    Finset SixVertexFourByFourAuditedHorizontalParameters :=
  Finset.univ.image sixVertexFourByFourAuditedCoordinateParameters


def sixVertexFourByFourAuditedCoordinateParameterComplement :
    Finset SixVertexFourByFourAuditedHorizontalParameters :=
  Finset.univ \ sixVertexFourByFourAuditedCoordinateParameterImage

end
end StatMech.FrontierD

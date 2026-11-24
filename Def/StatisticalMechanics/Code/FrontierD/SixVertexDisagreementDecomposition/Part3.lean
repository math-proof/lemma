module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairSwitchInterface.Part3
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementDecomposition.Part2
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementDecomposition.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def sixVertexLexPositiveSeamSeed
    (T : EvenTorus) (omega eta : SixVertexArrows T)
    (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty) :
    Fin T.width :=
  (sixVertexPositiveSeamDisagreements T omega eta).min' h

end
end StatMech.FrontierD

module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCheckerHorizontalBigrade
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairBigrade.Part2
public import Instance.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalCompletionBigrade
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalCompletionBigrade.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

abbrev SixVertexHorizontalField (T : EvenTorus) := T.Vertex -> Bool


end
end StatMech.FrontierD

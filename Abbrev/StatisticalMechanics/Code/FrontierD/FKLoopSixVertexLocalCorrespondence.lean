module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorTransferBridge.Part2
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
open Finset Matrix


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKLoopSixVertexLocalCorrespondence.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

abbrev FKMedialConfiguration (T : EvenTorus) := ConfigSpace T.Vertex


abbrev FKMedialLoopPairing (T : EvenTorus) := T.Vertex -> Bool

end StatMech.FrontierD

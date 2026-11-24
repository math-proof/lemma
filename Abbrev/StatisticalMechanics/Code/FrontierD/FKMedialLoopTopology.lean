module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKLoopSixVertexLocalCorrespondence.Part5
public import Inductive.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology
open SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTopology.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

abbrev FKMedialDart (T : EvenTorus) := T.Vertex × FKMedialSide


end StatMech.FrontierD

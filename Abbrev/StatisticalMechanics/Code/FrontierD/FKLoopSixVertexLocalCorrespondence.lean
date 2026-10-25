/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKLoopSixVertexLocalCorrespondence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorTransferBridge.Part2
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
open Finset Matrix


namespace StatMech.FrontierD

abbrev FKMedialConfiguration (T : EvenTorus) := ConfigSpace T.Vertex


abbrev FKMedialLoopPairing (T : EvenTorus) := T.Vertex -> Bool

end StatMech.FrontierD

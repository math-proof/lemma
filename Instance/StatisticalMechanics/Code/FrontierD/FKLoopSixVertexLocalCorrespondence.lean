module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorTransferBridge.Part2
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Def.StatisticalMechanics.Code.FrontierD.FKLoopSixVertexLocalCorrespondence
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

noncomputable instance fkLoopPairingCompatibleDecidable
    (pairing : Bool) (omega : SixVertexArrows T) (v : T.Vertex) :
    Decidable (fkLoopPairingCompatible pairing omega v) :=
  Classical.propDecidable _


end StatMech.FrontierD

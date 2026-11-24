module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorTransferBridge.Part2
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.FrontierD.FKLoopSixVertexLocalCorrespondence.Part2
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

noncomputable def fkOrientedLoopPairingWeight
    (lam : Real) (pairing : FKMedialLoopPairing T)
    (omega : SixVertexArrows T) : Real :=
  ∏ v, fkOrientedLoopLocalWeight lam (pairing v) omega v


noncomputable def fkOrientedLoopPartitionSum
    (T : EvenTorus) (lam : Real) : Real :=
  ∑ omega : SixVertexArrows T,
    ∑ pairing : FKMedialLoopPairing T,
      fkOrientedLoopPairingWeight lam pairing omega


end StatMech.FrontierD

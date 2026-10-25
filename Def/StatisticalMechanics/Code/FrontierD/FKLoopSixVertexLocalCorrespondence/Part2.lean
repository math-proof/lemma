/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKLoopSixVertexLocalCorrespondence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorTransferBridge.Part2
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Structure.StatisticalMechanics.Code.FrontierD.FKLoopSixVertexLocalCorrespondence
open Finset Matrix


namespace StatMech.FrontierD

def FKOrientedMedialLoops.toSixVertexConfiguration
    (loops : FKOrientedMedialLoops T) : SixVertexConfiguration T :=
  ⟨loops.arrows, fun v =>
    incomingCount_eq_two_of_fkLoopPairingCompatible
      (loops.pairing v) loops.arrows v (loops.compatible v)⟩


noncomputable def fkOrientedLoopLocalWeight
    (lam : Real) (pairing : Bool)
    (omega : SixVertexArrows T) (v : T.Vertex) : Real := by
  classical
  exact if fkLoopPairingCompatible pairing omega v then
      if omega.IsCType v then
        if pairing = fkLoopWestIncoming omega v then
          Real.exp (lam / 2) else Real.exp (-lam / 2)
      else 1
    else 0


end StatMech.FrontierD

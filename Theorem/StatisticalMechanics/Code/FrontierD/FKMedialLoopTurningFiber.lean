/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTurningFiber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialCheckerboard
import Def.StatisticalMechanics.Code.FrontierD.FKMedialLoopTurningFiber
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

variable {T : EvenTorus}

namespace FKMedialTurningFiber

theorem local_eq (lam : Real) (pairing : Bool) (a : SixVertexArrows T)
    (v : T.Vertex) (h : fkLoopPairingCompatible pairing a v) :
    fkOrientedLoopLocalWeight lam pairing a v =
      Real.exp ((lam / 4) * vertexTurn pairing a v) := by
  generalize hw : a.horizontal
    (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) = w at h ⊢
  generalize he : a.horizontal v = e at h ⊢
  generalize hs : a.vertical
    (v.1, SixVertexArrows.cyclicPred T.height_pos v.2) = s at h ⊢
  generalize hn : a.vertical v = n at h ⊢
  cases pairing <;> cases w <;> cases e <;> cases s <;> cases n <;>
    simp [fkOrientedLoopLocalWeight, fkLoopPairingCompatible,
      fkLoopWestIncoming, fkLoopEastIncoming, fkLoopSouthIncoming,
      fkLoopNorthIncoming, SixVertexArrows.IsCType, turnSign, vertexTurn,
      hw, he, hs, hn] at h ⊢ <;> ring_nf at *

end FKMedialTurningFiber
end
end StatMech.FrontierD

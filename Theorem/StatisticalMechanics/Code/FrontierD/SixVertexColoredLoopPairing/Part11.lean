/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairLoopFiber.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part8


namespace StatMech.FrontierD

noncomputable section

theorem fkColoredLocalPairOddCross_cTypeCount_of_odd
    (pair : FKColoredLocalPairing × FKColoredLocalPairing)
    (hodd : pair.1.west ^^ pair.1.east ^^
      pair.2.west ^^ pair.2.east = true) :
    fkColoredLocalPairCTypeCount (fkColoredLocalPairOddCross pair) =
      fkColoredLocalPairCTypeCount pair := by
  rcases pair with ⟨⟨p, a, b⟩, ⟨q, c, d⟩⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [fkColoredLocalPairCTypeCount, fkColoredLocalPairOddCross,
      fkColoredLocalPairCross, fkColoredLocalPairCrossWest] at hodd ⊢

@[simp] theorem fkColoredLocalPairReconnection_cTypeCount
    (pair : FKColoredLocalPairing × FKColoredLocalPairing) :
    fkColoredLocalPairCTypeCount (fkColoredLocalPairReconnection pair) =
      fkColoredLocalPairCTypeCount pair := by
  rcases pair with ⟨⟨p, a, b⟩, ⟨q, c, d⟩⟩
  by_cases hab : a = b <;> by_cases hcd : c = d <;>
    simp [fkColoredLocalPairCTypeCount, fkColoredLocalPairReconnection,
      add_comm, hab, hcd]

theorem FKColoredLoopPairingPair.localCTypeCount
    {T : EvenTorus} (source : FKColoredLoopPairingPair T) (v : T.Vertex) :
    fkColoredLocalPairCTypeCount
        ((source false).localPairing v, (source true).localPairing v) =
      (if (source false).arrows.IsCType v then 1 else 0) +
        (if (source true).arrows.IsCType v then 1 else 0) := by
  unfold fkColoredLocalPairCTypeCount FKColoredLoopPairing.localPairing
  change (if (source false).color (v, .west) =
        (source false).color (v, .east) then 1 else 0) +
      (if (source true).color (v, .west) =
        (source true).color (v, .east) then 1 else 0) = _
  rw [(source false).cType_iff_color_west_eq_east,
    (source true).cType_iff_color_west_eq_east]
  by_cases hfalse : (source false).color (v, .west) =
      (source false).color (v, .east) <;>
    by_cases htrue : (source true).color (v, .west) =
      (source true).color (v, .east) <;> simp [hfalse, htrue]

end
end StatMech.FrontierD

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairLoopFiber.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing


namespace StatMech.FrontierD

noncomputable section

def SixVertexCompatibleLoopPairing.toColored
    {T : EvenTorus} {omega : SixVertexArrows T}
    (pairing : SixVertexCompatibleLoopPairing omega) :
    FKColoredLoopPairing T where
  pairing := pairing.1
  color d := fkMedialCheckerColor d ^^ fkMedialDartIncoming omega d
  color_localMate := by
    intro d
    have hc := fkMedialCheckerColor_localMate_ne pairing.1 d
    have hi := fkMedialDartIncoming_localMate_ne pairing.1 omega pairing.2 d
    generalize hca : fkMedialCheckerColor
      (fkMedialLocalMate pairing.1 d) = ca at hc ⊢
    generalize hcb : fkMedialCheckerColor d = cb at hc ⊢
    generalize hia : fkMedialDartIncoming omega
      (fkMedialLocalMate pairing.1 d) = ia at hi ⊢
    generalize hib : fkMedialDartIncoming omega d = ib at hi ⊢
    exact boolXor_eq_of_ne_ne hc hi
  color_bondMate := by
    intro d
    have hc := fkMedialCheckerColor_bondMate_ne T d
    have hi := fkMedialDartIncoming_bondMate_ne T omega d
    generalize hca : fkMedialCheckerColor (fkMedialBondMate T d) = ca at hc ⊢
    generalize hcb : fkMedialCheckerColor d = cb at hc ⊢
    generalize hia : fkMedialDartIncoming omega
      (fkMedialBondMate T d) = ia at hi ⊢
    generalize hib : fkMedialDartIncoming omega d = ib at hi ⊢
    exact boolXor_eq_of_ne_ne hc hi

end
end StatMech.FrontierD

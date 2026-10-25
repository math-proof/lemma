/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialPrimalLabel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialToggleCount
import Def.StatisticalMechanics.Code.FrontierD.FKRectMedialPrimalLabel.Part2


namespace StatMech.FrontierD

theorem fkRectMedialDartPrimalLabel_localMate_closed
    (R : FKRectTorus) (d : FKMedialDart R.medialTorus) :
    fkRectMedialDartPrimalLabel R
        (fkMedialLocalMate (fkRectClosedMedialPairing R) d) =
      fkRectMedialDartPrimalLabel R d := by
  rcases d with ⟨v, side⟩
  cases hp : fkRectClosedPairingAtEdge (fkRectTorusMedialEdgeEquiv R v) <;>
    cases side <;>
    simp [fkRectMedialDartPrimalLabel, fkRectClosedMedialPairing,
      fkMedialLocalMate, hp]


theorem fkRectMedialDartPrimalLabel_localMate_reachable
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) :
    (fkRectOpenGraph R omega).Reachable
      (fkRectMedialDartPrimalLabel R d)
      (fkRectMedialDartPrimalLabel R
        (fkMedialLocalMate
          (fkRectConfigurationToMedialPairing R omega) d)) := by
  rcases d with ⟨v, side⟩
  let e := fkRectTorusMedialEdgeEquiv R v
  have hedge : fkRectTorusIndexedEdge R e =
      s(fkRectMedialWestPrimal R e, fkRectMedialEastPrimal R e) :=
    fkRectTorusIndexedEdge_eq_medialPrimals R e
  have hcross (ho : omega e = true) :
      (fkRectOpenGraph R omega).Reachable
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e) :=
    (show (fkRectOpenGraph R omega).Adj
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e) from
      ⟨e, ho, hedge⟩).reachable
  cases hopen : omega e <;>
    cases hp : fkRectClosedPairingAtEdge e <;> cases side
  all_goals
    simp only [fkRectConfigurationToMedialPairing_apply, e] at *
  all_goals
    simp [fkRectMedialDartPrimalLabel, fkMedialLocalMate, hopen, hp]
  all_goals
    first
    | exact SimpleGraph.Reachable.refl _
    | exact hcross hopen
    | exact (hcross hopen).symm

end StatMech.FrontierD

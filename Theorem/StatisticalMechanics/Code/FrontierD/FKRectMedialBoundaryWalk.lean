/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialBoundaryWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialReachability
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryPermutation.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareCoverIntersection.Part7
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectMedialDartPrimalLabel_localMate_eq_or_adj
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) :
    fkRectMedialDartPrimalLabel R d =
        fkRectMedialDartPrimalLabel R
          (fkMedialLocalMate
            (fkRectConfigurationToMedialPairing R omega) d) ∨
      (fkRectOpenGraph R omega).Adj
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
      (fkRectOpenGraph R omega).Adj
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e) :=
    ⟨e, ho, hedge⟩
  cases hopen : omega e <;>
    cases hp : fkRectClosedPairingAtEdge e <;> cases side
  all_goals
    simp only [fkRectConfigurationToMedialPairing_apply, e] at *
  all_goals
    simp [fkRectMedialDartPrimalLabel, fkMedialLocalMate, hopen, hp]
  all_goals
    first
    | exact Or.inl rfl
    | exact Or.inr (hcross hopen)
    | exact Or.inr (hcross hopen).symm


theorem fkRectMedialDartPrimalLabel_boundaryStep_eq_or_adj
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) :
    fkRectMedialDartPrimalLabel R d =
        fkRectMedialDartPrimalLabel R
          (fkMedialBoundaryStep
            (fkRectConfigurationToMedialPairing R omega) d) ∨
      (fkRectOpenGraph R omega).Adj
        (fkRectMedialDartPrimalLabel R d)
        (fkRectMedialDartPrimalLabel R
          (fkMedialBoundaryStep
            (fkRectConfigurationToMedialPairing R omega) d)) := by
  have h := fkRectMedialDartPrimalLabel_localMate_eq_or_adj R omega d
  rw [fkMedialBoundaryStep_apply,
    fkRectMedialDartPrimalLabel_bondMate] at ⊢
  exact h


end
end StatMech.FrontierD

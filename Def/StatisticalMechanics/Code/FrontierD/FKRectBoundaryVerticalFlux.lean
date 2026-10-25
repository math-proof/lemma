/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryVerticalFlux.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitWindingGeometry.Part10
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopVerticalWinding.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedAnchor.Part11
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryVerticalFlux
open Equiv Finset SimpleGraph
open StatMech.Onsager StatMech.Onsager.BaseCase


namespace StatMech.FrontierD

noncomputable section

def fkMedialVerticalSeamBlackDart
    (pairing : FKMedialLoopPairing T) (i : Fin T.width) :
    FKMedialBlackDart T := by
  let s := fkMedialVerticalSeamDart T i
  by_cases hs : fkMedialCheckerColor s = false
  · exact ⟨fkMedialLocalMate pairing (fkMedialBondMate T s), by
      have hbond := fkMedialCheckerColor_bondMate_ne T s
      have hlocal := fkMedialCheckerColor_localMate_ne pairing
        (fkMedialBondMate T s)
      rw [hs] at hbond
      generalize hb : fkMedialCheckerColor (fkMedialBondMate T s) = b
        at hbond hlocal
      generalize hl : fkMedialCheckerColor
        (fkMedialLocalMate pairing (fkMedialBondMate T s)) = c at hlocal
      cases b <;> cases c <;> simp_all⟩
  · exact ⟨fkMedialLocalMate pairing s, by
      rw [fkMedialCheckerColor_localMate_eq_not]
      simp [Bool.eq_true_of_not_eq_false hs]⟩


def fkMedialBlackVerticalSeamContribution
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T) : Int :=
  ∑ i : Fin T.width,
    if fkMedialVerticalSeamBlackDart pairing i = d then
      fkMedialCanonicalVerticalSeamSign T i
    else 0

end
end StatMech.FrontierD

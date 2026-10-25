/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitWindingGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnEssential
import Theorem.StatisticalMechanics.Code.Onsager.RectangularAxisSubdivision.Part8
import Def.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitWindingGeometry.Part5


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

noncomputable section

theorem fkRectBlackOrbitRibbonSubdivisionDart_valid
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    ∀ k,
      (fkRectBlackOrbitRibbonSubdivisionDart R omega d k).1 =
        ons_dirStep (fkRectBlackOrbitRibbonSubdivisionSide R)
          (fkRectBlackOrbitRibbonSubdivisionDart R omega d (k + 1)).2
          (fkRectBlackOrbitRibbonSubdivisionDart R omega d (k + 1)).1 := by
  let word := fkRectBlackOrbitRibbonSubdivisionWord R omega d
  let w := fkRectWalkWinding R
    (fkRectBlackBoundaryPrimalCycleWalk R omega d)
  have hw :=
    fkRectBlackOrbitRibbonSubdivisionWord_preserves_winding R omega d
  have hdisp : (word.map stepOf).sum =
      ((fkRectBlackOrbitRibbonSubdivisionSide R : ℤ) * w.1,
        (fkRectBlackOrbitRibbonSubdivisionSide R : ℤ) * w.2) := by
    apply Prod.ext
    · rw [onsDirectionWord_stepOf_fst_sum]
      exact hw.1
    · rw [onsDirectionWord_stepOf_snd_sum]
      exact hw.2
  simpa only [fkRectBlackOrbitRibbonSubdivisionDart, word] using
    (onsDirectionWordTorusDart_valid
      (fkRectBlackOrbitRibbonSubdivisionSide R) word w.1 w.2 hdisp)

theorem fkRectBlackOrbitRibbonSubdivisionDart_exponentX_sum
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    let w := fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)
    (∑ k, ons_dirExponentX
      (fkRectBlackOrbitRibbonSubdivisionDart R omega d k).2) =
        (fkRectBlackOrbitRibbonSubdivisionSide R : ℤ) * w.1 := by
  dsimp only
  rw [show (∑ k, ons_dirExponentX
      (fkRectBlackOrbitRibbonSubdivisionDart R omega d k).2) =
      ((fkRectBlackOrbitRibbonSubdivisionWord R omega d).map
        ons_dirExponentX).sum by
    simpa only [fkRectBlackOrbitRibbonSubdivisionDart] using
      (onsDirectionWordTorusDart_exponentX_sum
        (fkRectBlackOrbitRibbonSubdivisionSide R)
        (fkRectBlackOrbitRibbonSubdivisionWord R omega d))]
  exact (fkRectBlackOrbitRibbonSubdivisionWord_preserves_winding
    R omega d).1

theorem fkRectBlackOrbitRibbonSubdivisionDart_exponentY_sum
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    let w := fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)
    (∑ k, ons_dirExponentY
      (fkRectBlackOrbitRibbonSubdivisionDart R omega d k).2) =
        (fkRectBlackOrbitRibbonSubdivisionSide R : ℤ) * w.2 := by
  dsimp only
  rw [show (∑ k, ons_dirExponentY
      (fkRectBlackOrbitRibbonSubdivisionDart R omega d k).2) =
      ((fkRectBlackOrbitRibbonSubdivisionWord R omega d).map
        ons_dirExponentY).sum by
    simpa only [fkRectBlackOrbitRibbonSubdivisionDart] using
      (onsDirectionWordTorusDart_exponentY_sum
        (fkRectBlackOrbitRibbonSubdivisionSide R)
        (fkRectBlackOrbitRibbonSubdivisionWord R omega d))]
  exact (fkRectBlackOrbitRibbonSubdivisionWord_preserves_winding
    R omega d).2


end
end StatMech.FrontierD

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitWindingGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnEssential
import Theorem.StatisticalMechanics.Code.Onsager.RectangularAxisSubdivision.Part8
import Instance.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitWindingGeometry


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

noncomputable section

theorem fkRectBlackOrbitRibbonSubdivisionWord_preserves_winding
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    let w := fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)
    ((fkRectBlackOrbitRibbonSubdivisionWord R omega d).map
        ons_dirExponentX).sum =
          (fkRectBlackOrbitRibbonSubdivisionSide R : ℤ) * w.1 ∧
      ((fkRectBlackOrbitRibbonSubdivisionWord R omega d).map
        ons_dirExponentY).sum =
          (fkRectBlackOrbitRibbonSubdivisionSide R : ℤ) * w.2 := by
  dsimp only
  let word := fkRectBlackOrbitMedialRibbonWord R omega d
  let w := fkRectWalkWinding R
    (fkRectBlackBoundaryPrimalCycleWalk R omega d)
  have hstep := fkRectBlackOrbitMedialRibbonWord_step_sum R omega d
  change (word.map stepOf).sum =
    (8 * ((2 * R.width : ℕ) : ℤ) * w.1,
      8 * (R.height : ℤ) * w.2) at hstep
  have hx : (word.map ons_dirExponentX).sum =
      ((16 * R.width : ℕ) : ℤ) * w.1 := by
    have h := congrArg Prod.fst hstep
    rw [onsDirectionWord_stepOf_fst_sum] at h
    calc
      _ = 8 * ((2 * R.width : ℕ) : ℤ) * w.1 := by
        simpa only [Prod.fst] using h
      _ = ((16 * R.width : ℕ) : ℤ) * w.1 := by
        push_cast
        ring
  have hy : (word.map ons_dirExponentY).sum =
      ((8 * R.height : ℕ) : ℤ) * w.2 := by
    have h := congrArg Prod.snd hstep
    rw [onsDirectionWord_stepOf_snd_sum] at h
    simpa only [Prod.snd, Nat.cast_mul, Nat.cast_ofNat] using h
  have h := onsAnisotropicDirectionWord_preserves_winding
    (16 * R.width) (8 * R.height) word w.1 w.2 hx hy
  simpa [fkRectBlackOrbitRibbonSubdivisionWord,
    fkRectBlackOrbitRibbonSubdivisionSide, word, w] using h


end
end StatMech.FrontierD

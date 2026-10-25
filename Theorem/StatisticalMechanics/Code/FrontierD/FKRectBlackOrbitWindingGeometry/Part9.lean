/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitWindingGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnEssential
import Theorem.StatisticalMechanics.Code.Onsager.RectangularAxisSubdivision.Part8
import Def.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitWindingGeometry.Part7


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

noncomputable section

theorem fkRectBlackOrbitShearSubdivisionWord_preserves_winding
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    let w := fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)
    ((fkRectBlackOrbitShearSubdivisionWord R omega d).map
        ons_dirExponentX).sum =
          (fkRectBlackOrbitSubdivisionSide R : ℕ) * w.1 ∧
      ((fkRectBlackOrbitShearSubdivisionWord R omega d).map
        ons_dirExponentY).sum =
          (fkRectBlackOrbitSubdivisionSide R : ℕ) * w.2 := by
  dsimp only
  let pairing := fkRectConfigurationToMedialPairing R omega
  let word := List.ofFn (fkRectBlackOrbitDirection pairing d)
  let w := fkRectWalkWinding R
    (fkRectBlackBoundaryPrimalCycleWalk R omega d)
  have hdisp := fkRectBlackOrbitDisplacement_eq_two_deck_winding R omega d
  change ons_pathDisplacement word = 2 • fkRectSquareDeckTranslation R w at hdisp
  have hrect : ons_pathDisplacement word =
      ((2 * R.width : ℕ) * w.1 + (R.height : ℤ) * w.2,
        (2 * R.width : ℕ) * w.1 - (R.height : ℤ) * w.2) := by
    have hheight : (2 : ℤ) * (R.height / 2 : ℕ) = R.height := by
      exact_mod_cast Nat.two_mul_div_two_of_even R.height_even
    rw [hdisp]
    apply Prod.ext
    · change 2 * ((R.width : ℤ) * w.1 +
          ((R.height / 2 : ℕ) : ℤ) * w.2) =
        ((2 * R.width : ℕ) : ℤ) * w.1 + (R.height : ℤ) * w.2
      rw [Nat.cast_mul, Nat.cast_ofNat]
      linear_combination w.2 * hheight
    · change 2 * ((R.width : ℤ) * w.1 -
          ((R.height / 2 : ℕ) : ℤ) * w.2) =
        ((2 * R.width : ℕ) : ℤ) * w.1 - (R.height : ℤ) * w.2
      rw [Nat.cast_mul, Nat.cast_ofNat]
      linear_combination -(w.2 * hheight)
  have hrect' : (word.map stepOf).sum =
      ((2 * R.width : ℕ) * w.1 + (R.height : ℤ) * w.2,
        (2 * R.width : ℕ) * w.1 - (R.height : ℤ) * w.2) := by
    rw [← ons_pathDisplacement_eq_sum_map]
    exact hrect
  have h := onsRectangularShearSubdivisionWord_preserves_deck_winding
    R.width R.height word w.1 w.2 hrect'
  simpa [fkRectBlackOrbitShearSubdivisionWord,
    fkRectBlackOrbitSubdivisionSide, pairing, word, w] using h


end
end StatMech.FrontierD

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentOrbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoComponentStrand.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitComponentOrbitHall.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentOrbit
open Finset
open scoped symmDiff


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexPositiveUnitComponentOrbitBase

variable {T : EvenTorus} {middle : Fin (T.width + 1)} {k : Nat}


def source
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    (positive : BooleanLayer
      (SixVertexDisagreementComponent base.first base.second) (k + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) :
    SixVertexConfigurationPhysicalSource T middle hmiddle_pos hmiddle_lt := by
  let mask := base.mask positive
  have hfull := base.mask_full positive
  have hkpos := base.k_pos
  have hk := base.k_le_middle
  have htransfer : sixVertexTorusMaskSeamTransfer mask
      base.first base.second = ((k - 1 : Nat) : Int) := by
    rw [show mask = base.mask positive by rfl, base.mask_seamTransfer]
    omega
  have hfirstCount : sixVertexUpCount
      (svTorusVerticalRows T
        (sixVertexTorusSwitchFirst mask base.first base.second)
        (svFinLast T.height_pos)) = middle.val - 1 := by
    have hcount : (sixVertexUpCount
        (svTorusVerticalRows T
          (sixVertexTorusSwitchFirst mask base.first base.second)
          (svFinLast T.height_pos)) : Int) =
        ((middle.val - 1 : Nat) : Int) := by
      rw [intCast_upCount_switchFirst_eq_add_seamTransfer,
        base.firstSector, htransfer]
      omega
    exact_mod_cast hcount
  have hsecondCount : sixVertexUpCount
      (svTorusVerticalRows T
        (sixVertexTorusSwitchSecond mask base.first base.second)
        (svFinLast T.height_pos)) = middle.val + 1 := by
    have hcount : (sixVertexUpCount
        (svTorusVerticalRows T
          (sixVertexTorusSwitchSecond mask base.first base.second)
          (svFinLast T.height_pos)) : Int) =
        ((middle.val + 1 : Nat) : Int) := by
      rw [intCast_upCount_switchSecond_eq_sub_seamTransfer,
        base.secondSector, htransfer]
      push_cast
      omega
    exact_mod_cast hcount
  exact
    (⟨sixVertexTorusSwitchFirst mask base.first base.second,
      hfull.switchFirst_ice base.firstIce base.secondIce, hfirstCount⟩,
    ⟨sixVertexTorusSwitchSecond mask base.first base.second,
      hfull.switchSecond_ice base.firstIce base.secondIce, hsecondCount⟩)


def target
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    (positive : BooleanLayer
      (SixVertexDisagreementComponent base.first base.second) k) :
    SixVertexConfigurationPhysicalTarget T middle := by
  let mask := base.mask positive
  have hfull := base.mask_full positive
  have hk := base.k_le_middle
  have htransfer : sixVertexTorusMaskSeamTransfer mask
      base.first base.second = (k : Int) := by
    rw [show mask = base.mask positive by rfl, base.mask_seamTransfer]
    omega
  have hfirstCount : sixVertexUpCount
      (svTorusVerticalRows T
        (sixVertexTorusSwitchFirst mask base.first base.second)
        (svFinLast T.height_pos)) = middle.val := by
    have hcount : (sixVertexUpCount
        (svTorusVerticalRows T
          (sixVertexTorusSwitchFirst mask base.first base.second)
          (svFinLast T.height_pos)) : Int) = (middle.val : Int) := by
      rw [intCast_upCount_switchFirst_eq_add_seamTransfer,
        base.firstSector, htransfer]
      omega
    exact_mod_cast hcount
  have hsecondCount : sixVertexUpCount
      (svTorusVerticalRows T
        (sixVertexTorusSwitchSecond mask base.first base.second)
        (svFinLast T.height_pos)) = middle.val := by
    have hcount : (sixVertexUpCount
        (svTorusVerticalRows T
          (sixVertexTorusSwitchSecond mask base.first base.second)
          (svFinLast T.height_pos)) : Int) = (middle.val : Int) := by
      rw [intCast_upCount_switchSecond_eq_sub_seamTransfer,
        base.secondSector, htransfer]
      push_cast
      omega
    exact_mod_cast hcount
  exact
    (⟨sixVertexTorusSwitchFirst mask base.first base.second,
      hfull.switchFirst_ice base.firstIce base.secondIce, hfirstCount⟩,
    ⟨sixVertexTorusSwitchSecond mask base.first base.second,
      hfull.switchSecond_ice base.firstIce base.secondIce, hsecondCount⟩)

end SixVertexPositiveUnitComponentOrbitBase
end
end StatMech.FrontierD

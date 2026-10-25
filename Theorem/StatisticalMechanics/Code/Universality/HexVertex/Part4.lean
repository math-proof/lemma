/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Universality.HexVertex.Part3


namespace StatMech.Universality

open Complex


theorem hexPairContribution_zero (du : ℂ) (k : ℤ) (n : ℕ) :
    hexContribution (hexOmega * du) (k - 4) n
      + hexContribution (hexOmega ^ 2 * du) (k + 4) n = 0 := by
  unfold hexContribution
  have hlne : hexLambda ≠ 0 := by
    unfold hexLambda; exact Complex.exp_ne_zero _
  
  rw [show hexLambda ^ (k - 4) = hexLambda ^ k * hexLambda ^ (-4 : ℤ) by
        rw [sub_eq_add_neg, zpow_add₀ hlne],
      show hexLambda ^ (k + 4) = hexLambda ^ k * hexLambda ^ (4 : ℤ) by
        rw [zpow_add₀ hlne]]
  have key := hexPair_zero
  
  
  calc
    hexOmega * du * (hexLambda ^ k * hexLambda ^ (-4 : ℤ)) * (hexChi : ℂ) ^ n
        + hexOmega ^ 2 * du * (hexLambda ^ k * hexLambda ^ (4 : ℤ)) * (hexChi : ℂ) ^ n
      = (du * hexLambda ^ k * (hexChi : ℂ) ^ n)
          * (hexOmega * hexLambda ^ (-4 : ℤ) + hexOmega ^ 2 * hexLambda ^ (4 : ℤ)) := by ring
    _ = (du * hexLambda ^ k * (hexChi : ℂ) ^ n) * 0 := by rw [key]
    _ = 0 := by ring


theorem hexTripletContribution_zero (du : ℂ) (k : ℤ) (n : ℕ) :
    hexContribution du k n
      + hexContribution (hexOmega * du) (k - 1) (n + 1)
      + hexContribution (hexOmega ^ 2 * du) (k + 1) (n + 1) = 0 := by
  unfold hexContribution
  have hlne : hexLambda ≠ 0 := by
    unfold hexLambda; exact Complex.exp_ne_zero _
  rw [show hexLambda ^ (k - 1) = hexLambda ^ k * hexLambda ^ (-1 : ℤ) by
        rw [sub_eq_add_neg, zpow_add₀ hlne],
      show hexLambda ^ (k + 1) = hexLambda ^ k * hexLambda ^ (1 : ℤ) by
        rw [zpow_add₀ hlne],
      pow_succ]
  have key := hexTriplet_zero
  calc
    du * hexLambda ^ k * (hexChi : ℂ) ^ n
        + hexOmega * du * (hexLambda ^ k * hexLambda ^ (-1 : ℤ)) * ((hexChi : ℂ) ^ n * (hexChi : ℂ))
        + hexOmega ^ 2 * du * (hexLambda ^ k * hexLambda ^ (1 : ℤ)) * ((hexChi : ℂ) ^ n * (hexChi : ℂ))
      = (du * hexLambda ^ k * (hexChi : ℂ) ^ n)
          * (1 + (hexChi : ℂ) * (hexOmega * hexLambda ^ (-1 : ℤ))
              + (hexChi : ℂ) * (hexOmega ^ 2 * hexLambda ^ (1 : ℤ))) := by ring
    _ = (du * hexLambda ^ k * (hexChi : ℂ) ^ n) * 0 := by rw [key]
    _ = 0 := by ring


end StatMech.Universality

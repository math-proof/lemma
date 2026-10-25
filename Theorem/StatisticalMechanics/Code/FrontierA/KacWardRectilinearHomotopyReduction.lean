/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearHomotopyReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngleHomotopy.Part3


namespace StatMech.FrontierA

open scoped BigOperators

open Set

open StatMech.Onsager.BaseCase

theorem arg_posReal_mul_rectilinear
    (s : ℝ) (hs : 0 < s) (z : ℂ) (hz : z ≠ 0) :
    Complex.arg ((s : ℂ) * z) = Complex.arg z := by
  have harg : Complex.arg (s : ℂ) = 0 :=
    Complex.arg_ofReal_of_nonneg hs.le
  have hmem : Complex.arg (s : ℂ) + Complex.arg z ∈
      Set.Ioc (-Real.pi) Real.pi := by
    rw [harg, zero_add]
    exact ⟨Complex.neg_pi_lt_arg z, Complex.arg_le_pi z⟩
  rw [Complex.arg_mul (Complex.ofReal_ne_zero.mpr hs.ne') hz hmem,
    harg, zero_add]


theorem kwVectorTurnPhase_pos_scales
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (z w : ℂ) (hz : z ≠ 0) (hw : w ≠ 0) :
    kwVectorTurnPhase ((s : ℂ) * z) ((t : ℂ) * w) =
      kwVectorTurnPhase z w := by
  unfold kwVectorTurnPhase kwAngleTurnPhase
  rw [arg_posReal_mul_rectilinear s hs z hz,
    arg_posReal_mul_rectilinear t ht w hw]


end StatMech.FrontierA

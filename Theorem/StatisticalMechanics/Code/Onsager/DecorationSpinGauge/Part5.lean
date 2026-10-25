/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSpinGauge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationInternalMiddle.Part3
import Theorem.StatisticalMechanics.Code.Onsager.TorusLoopHomology.Part2
import Def.StatisticalMechanics.Code.Onsager.DecorationSpinGauge.Part4


namespace StatMech.Onsager

open BigOperators

theorem ons_decMiddleStateGauge_ne_zero
    (L : ℕ) (a b : Fin 2) (site : ZMod L × ZMod L) :
    ∀ state, ons_decMiddleStateGauge L a b site state ≠ 0 := by
  rintro (d | side)
  · exact ons_spinVertexGauge_ne_zero L a b d.1
  · exact ons_spinVertexGauge_ne_zero L a b site

theorem ons_decMiddleU_spinGauge
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (omega : ℂ) (site : ZMod L × ZMod L)
    (d : ons_Dart L) (side : Fin 2) :
    ons_decMiddleU L decWeight omega site d side =
      ons_spinVertexGauge L a b d.1 *
        ons_decMiddleU L (ons_spinSeamDecWeight decWeight a b)
          omega site d side *
        (ons_spinVertexGauge L a b site)⁻¹ := by
  rw [ons_decMiddleU_spinSeam]
  unfold ons_decMiddleU
  by_cases h : d.1 = site ∧ ons_decMiddleSide d.2 = side
  · simp only [h, true_and, if_true]
    have hne := ons_spinVertexGauge_ne_zero L a b site
    field_simp [hne]
  · simp [h]


theorem ons_decMiddleAugmented_spinGauge
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (omega t : ℂ) (site : ZMod L × ZMod L) :
    ons_decMiddleAugmented L decWeight omega
        (ons_spinPhase L a) (ons_spinPhase L b) t site =
      ons_diagonalGaugeMatrix
        (ons_decMiddleStateGauge L a b site)
        (ons_decMiddleAugmented L
          (ons_spinSeamDecWeight decWeight a b)
          omega 1 1 t site) := by
  ext i j
  cases i with
  | inl d₂ =>
      cases j with
      | inl d₁ =>
          have hmatrix := congrFun₂
            (ons_KWmatDecorationWeightedPhase_spinGauge
              L (ons_scaleDecEdgeWeight decWeight
                (ons_decChainEdge site 1) 0) a b omega) d₂ d₁
          simpa [ons_decMiddleAugmented, ons_diagonalGaugeMatrix,
            ons_decMiddleStateGauge,
            ons_spinSeamDecWeight_scale_chain_one] using hmatrix
      | inr side =>
          simpa [ons_decMiddleAugmented, ons_diagonalGaugeMatrix,
            ons_decMiddleStateGauge] using
            ons_decMiddleU_spinGauge
              L decWeight a b omega site d₂ side
  | inr side =>
      cases j with
      | inl d₁ =>
          have hV := congrFun₂
            (ons_decMiddleV_spinGauge
              L decWeight a b omega site) side d₁
          simp only [ons_decMiddleAugmented,
            ons_diagonalGaugeMatrix, ons_decMiddleStateGauge,
            Matrix.fromBlocks_apply₂₁, Matrix.smul_apply, smul_eq_mul]
          rw [hV]
          ring
      | inr side' =>
          simp [ons_decMiddleAugmented, ons_diagonalGaugeMatrix,
            ons_decMiddleStateGauge]

end StatMech.Onsager

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSpinGauge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationInternalMiddle.Part3
import Theorem.StatisticalMechanics.Code.Onsager.TorusLoopHomology.Part2
import Def.StatisticalMechanics.Code.Onsager.DecorationSpinGauge.Part3


namespace StatMech.Onsager

open BigOperators

theorem ons_loopWeight_diagonalGaugeMatrix
    {E : Type*} [Fintype E] [DecidableEq E]
    {n : ℕ} [NeZero n] (gauge : E → ℂ)
    (hgauge : ∀ e, gauge e ≠ 0) (M : Matrix E E ℂ)
    (loop : Fin n → E) :
    ons_loopWeight (ons_diagonalGaugeMatrix gauge M) loop =
      ons_loopWeight M loop := by
  unfold ons_loopWeight ons_diagonalGaugeMatrix
  simp_rw [mul_assoc]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have hreindex : (∏ k, gauge (loop (k + 1))) =
      ∏ k, gauge (loop k) :=
    Equiv.prod_comp (Equiv.addRight (1 : Fin n))
      (fun k ↦ gauge (loop k))
  rw [Finset.prod_inv_distrib, hreindex]
  have hprod : (∏ k, gauge (loop k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun k hk ↦ hgauge _)
  calc
    (∏ x, gauge (loop x)) *
          ((∏ x, M (loop x) (loop (x + 1))) *
            (∏ k, gauge (loop k))⁻¹) =
        (∏ x, M (loop x) (loop (x + 1))) *
          ((∏ k, gauge (loop k)) *
            (∏ k, gauge (loop k))⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hprod, mul_one]

theorem ons_decTransitionWeight_spinSeam
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (d₂ d₁ : ons_Dart L) :
    ons_decTransitionWeight L (ons_spinSeamDecWeight decWeight a b) d₂ d₁ =
      ons_spinDartSeamSign a b d₁ *
        ons_decTransitionWeight L decWeight d₂ d₁ := by
  unfold ons_decTransitionWeight
  rw [ons_spinSeamDecWeight_external]
  have hchain :
      (∏ i ∈ ons_decChainPathIndices (d₁.2 + 2) d₂.2,
        ons_spinSeamDecWeight decWeight a b
          (ons_decChainEdge d₂.1 i)) =
        ∏ i ∈ ons_decChainPathIndices (d₁.2 + 2) d₂.2,
          decWeight (ons_decChainEdge d₂.1 i) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [ons_spinSeamDecWeight_chain]
  rw [hchain]
  ring


theorem ons_KWmatDecorationWeightedPhase_spinGauge
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (omega : ℂ) :
    ons_KWmatDecorationWeightedPhase L decWeight omega
        (ons_spinPhase L a) (ons_spinPhase L b) =
      ons_diagonalGaugeMatrix
        (fun d : ons_Dart L ↦ ons_spinVertexGauge L a b d.1)
        (ons_KWmatDecorationWeightedPhase L
          (ons_spinSeamDecWeight decWeight a b) omega 1 1) := by
  ext d₂ d₁
  by_cases hstep : d₂.1 = ons_dirStep L d₁.2 d₁.1
  · have hg := ons_dirPhase_spin_mul_vertexGauge L a b d₁
    have hne := ons_spinVertexGauge_ne_zero L a b d₁.1
    unfold ons_diagonalGaugeMatrix
    simp only
    unfold ons_KWmatDecorationWeightedPhase
    simp only [hstep, if_pos, ons_dirPhase_one_one, one_mul]
    rw [ons_decTransitionWeight_spinSeam]
    field_simp [hne]
    linear_combination hg *
      (ons_decTransitionWeight L decWeight d₂ d₁ *
        ons_turnW omega d₁.2 d₂.2)
  · unfold ons_KWmatDecorationWeightedPhase ons_diagonalGaugeMatrix
    simp [hstep]

theorem ons_decMiddleU_spinSeam
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (omega : ℂ) (site : ZMod L × ZMod L) :
    ons_decMiddleU L (ons_spinSeamDecWeight decWeight a b) omega site =
      ons_decMiddleU L decWeight omega site := by
  ext d side
  rcases d with ⟨p, mu⟩
  fin_cases mu <;>
    simp [ons_decMiddleU, ons_decMiddleDestFactor]

theorem ons_decMiddleSourceFactor_spinSeam
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (site : ZMod L × ZMod L) (mu : Fin 4) :
    ons_decMiddleSourceFactor (ons_spinSeamDecWeight decWeight a b)
        site mu =
      ons_decMiddleSourceFactor decWeight site mu := by
  fin_cases mu <;>
    simp [ons_decMiddleSourceFactor]

theorem ons_decMiddleV_spinGauge
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (omega : ℂ) (site : ZMod L × ZMod L) :
    ons_decMiddleV L decWeight omega
        (ons_spinPhase L a) (ons_spinPhase L b) site =
      fun side d ↦
        ons_spinVertexGauge L a b site *
          ons_decMiddleV L (ons_spinSeamDecWeight decWeight a b)
            omega 1 1 site side d *
          (ons_spinVertexGauge L a b d.1)⁻¹ := by
  ext side d
  unfold ons_decMiddleV
  by_cases h : site = ons_dirStep L d.2 d.1 ∧
      ons_decMiddleSide d.2 = side
  · rw [if_pos h, if_pos h]
    rw [ons_spinSeamDecWeight_chain,
      ons_spinSeamDecWeight_external,
      ons_decMiddleSourceFactor_spinSeam]
    simp only [ons_dirPhase_one_one, one_mul]
    have hg := ons_dirPhase_spin_mul_vertexGauge L a b d
    rw [← h.1] at hg
    have hne := ons_spinVertexGauge_ne_zero L a b d.1
    field_simp [hne]
    linear_combination hg *
      (decWeight (ons_decChainEdge site 1) *
        decWeight s(d, ons_dartRev L d) *
        ons_decMiddleSourceFactor decWeight site d.2 *
        ons_turnW omega d.2 (ons_decMiddleDir side))
  · rw [if_neg h, if_neg h]
    ring

theorem ons_spinSeamDecWeight_scale_chain_one
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (site : ZMod L × ZMod L) (t : ℂ) :
    ons_spinSeamDecWeight
        (ons_scaleDecEdgeWeight decWeight
          (ons_decChainEdge site 1) t) a b =
      ons_scaleDecEdgeWeight
        (ons_spinSeamDecWeight decWeight a b)
        (ons_decChainEdge site 1) t := by
  funext edge
  classical
  by_cases hext : ons_decIsExternal edge
  · have hne : edge ≠ ons_decChainEdge site 1 := by
      intro heq
      apply ons_decChainEdge_not_external L site 1
      rwa [← heq]
    simp [ons_spinSeamDecWeight, ons_scaleDecEdgeWeight, hext, hne]
  · simp [ons_spinSeamDecWeight, ons_scaleDecEdgeWeight, hext]

end StatMech.Onsager

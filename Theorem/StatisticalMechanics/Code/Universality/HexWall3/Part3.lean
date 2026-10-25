/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexWall3.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexConnClosed
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeFull.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeWeight.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexSurgerySeams.Part5
import Def.StatisticalMechanics.Code.Universality.HexWall3.Part3


namespace StatMech.Universality

open HexWalk List Filter Topology

open scoped BigOperators Topology Real NNReal


theorem hexWall3_witness_mem (a : ℂ) :
    hexWall3_mem a 0 1 [(-1 : ℤ)] :=
  hexWall3_bridge_mem a 0 hexWall3_witnessBridge
    (hexWall3_reachesWidth_witness a) (hexWall3_isLegalSAW_witness a)


theorem hexWall3_bridgeProd_le (bs : List HexBridge) (h : StrictDecreasingWidths bs)
    (υ : ℕ → ℝ) (wtBr : HexBridge → ℝ)
    (hdom : ∀ b ∈ bs, wtBr b ≤ υ b.width)
    (hwtnn : ∀ b ∈ bs, 0 ≤ wtBr b) :
    (bs.map wtBr).prod ≤ ∏ T ∈ hbw_widthFinset bs, υ T := by
  rw [← hbw_prod_eq_finsetProd bs h υ]
  exact List.prod_map_le_prod_map₀ wtBr (fun b => υ b.width) hwtnn hdom


theorem hexWall3_weightBound_factor (x g : ℝ) (hx : 0 < x)
    (lower upper : List HexBridge)
    (hlo : StrictDecreasingWidths lower) (hup : StrictDecreasingWidths upper)
    (υ : ℕ → ℝ) (wtBr : HexBridge → ℝ)
    (hdomLo : ∀ b ∈ lower, wtBr b ≤ υ b.width)
    (hdomUp : ∀ b ∈ upper, wtBr b ≤ υ b.width)
    (hwtnn : ∀ b, 0 ≤ wtBr b)
    (htwo : g * x ^ 2 = (lower.map wtBr).prod * (upper.map wtBr).prod) :
    g ≤ (x ^ 2)⁻¹ *
      ((∏ T ∈ hbw_widthFinset lower, υ T) * (∏ T ∈ hbw_widthFinset upper, υ T)) := by
  have hloProd : (lower.map wtBr).prod ≤ ∏ T ∈ hbw_widthFinset lower, υ T :=
    hexWall3_bridgeProd_le lower hlo υ wtBr hdomLo (fun b _ => hwtnn b)
  have hupProd : (upper.map wtBr).prod ≤ ∏ T ∈ hbw_widthFinset upper, υ T :=
    hexWall3_bridgeProd_le upper hup υ wtBr hdomUp (fun b _ => hwtnn b)
  have hloNN : (0 : ℝ) ≤ (lower.map wtBr).prod :=
    List.prod_nonneg (by
      intro y hy; simp only [List.mem_map] at hy; obtain ⟨b, _, rfl⟩ := hy; exact hwtnn _)
  have hupNN : (0 : ℝ) ≤ (upper.map wtBr).prod :=
    List.prod_nonneg (by
      intro y hy; simp only [List.mem_map] at hy; obtain ⟨b, _, rfl⟩ := hy; exact hwtnn _)
  have hg : g = (x ^ 2)⁻¹ * ((lower.map wtBr).prod * (upper.map wtBr).prod) := by
    have hx2 : (0 : ℝ) < x ^ 2 := by positivity
    field_simp at htwo ⊢; linarith [htwo]
  rw [hg]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact mul_le_mul hloProd hupProd hupNN (le_trans hloNN hloProd)


end StatMech.Universality

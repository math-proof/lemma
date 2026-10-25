/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeWeight.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame
import Theorem.StatisticalMechanics.Code.Universality.HexBridge.Part6
import Def.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part9
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexSurgerySeams.Part5
import Def.StatisticalMechanics.Code.Universality.HexBridgeWeight


namespace StatMech.Universality

open List

open scoped BigOperators


theorem hbw_prod_eq_finsetProd (bs : List HexBridge) (h : StrictDecreasingWidths bs)
    (υ : ℕ → ℝ) :
    (bs.map (fun b => υ b.width)).prod = ∏ T ∈ hbw_widthFinset bs, υ T := by
  have hnd := hbw_widthlist_nodup bs h
  unfold hbw_widthFinset
  rw [List.prod_toFinset υ hnd, List.map_map]
  rfl


theorem hbw_bridgeProd_le (bs : List HexBridge) (h : StrictDecreasingWidths bs)
    (υ wt : ℕ → ℝ) (hdom : ∀ b ∈ bs, wt b.width ≤ υ b.width)
    (hwtnn : ∀ b ∈ bs, 0 ≤ wt b.width) :
    (bs.map (fun b => wt b.width)).prod ≤ ∏ T ∈ hbw_widthFinset bs, υ T := by
  rw [← hbw_prod_eq_finsetProd bs h υ]
  exact List.prod_map_le_prod_map₀ (fun b => wt b.width) (fun b => υ b.width)
    (fun b hb => hwtnn b hb) (fun b hb => hdom b hb)


theorem hbw_weightBound_factor (x g : ℝ) (hx : 0 < x)
    (lower upper : List HexBridge)
    (hlo : StrictDecreasingWidths lower) (hup : StrictDecreasingWidths upper)
    (υ wt : ℕ → ℝ)
    (hdomLo : ∀ b ∈ lower, wt b.width ≤ υ b.width)
    (hdomUp : ∀ b ∈ upper, wt b.width ≤ υ b.width)
    (hwtnn : ∀ T, 0 ≤ wt T)
    (htwo : g * x ^ 2 = (lower.map (fun b => wt b.width)).prod
                          * (upper.map (fun b => wt b.width)).prod) :
    g ≤ (x ^ 2)⁻¹ *
      ((∏ T ∈ hbw_widthFinset lower, υ T) * (∏ T ∈ hbw_widthFinset upper, υ T)) := by
  have hloProd : (lower.map (fun b => wt b.width)).prod ≤ ∏ T ∈ hbw_widthFinset lower, υ T :=
    hbw_bridgeProd_le lower hlo υ wt hdomLo (fun b _ => hwtnn b.width)
  have hupProd : (upper.map (fun b => wt b.width)).prod ≤ ∏ T ∈ hbw_widthFinset upper, υ T :=
    hbw_bridgeProd_le upper hup υ wt hdomUp (fun b _ => hwtnn b.width)
  have hloNN : (0 : ℝ) ≤ (lower.map (fun b => wt b.width)).prod :=
    List.prod_nonneg (by
      intro y hy; simp only [List.mem_map] at hy; obtain ⟨b, _, rfl⟩ := hy; exact hwtnn _)
  have hupNN : (0 : ℝ) ≤ (upper.map (fun b => wt b.width)).prod :=
    List.prod_nonneg (by
      intro y hy; simp only [List.mem_map] at hy; obtain ⟨b, _, rfl⟩ := hy; exact hwtnn _)
  have hx2 : (0 : ℝ) < x ^ 2 := by positivity
  
  have hg : g = (x ^ 2)⁻¹ * ((lower.map (fun b => wt b.width)).prod
                          * (upper.map (fun b => wt b.width)).prod) := by
    field_simp at htwo ⊢
    linarith [htwo]
  rw [hg]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact mul_le_mul hloProd hupProd hupNN (le_trans hloNN hloProd)


end StatMech.Universality

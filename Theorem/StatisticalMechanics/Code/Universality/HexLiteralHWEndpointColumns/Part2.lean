/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWEndpointColumns.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part14
import Theorem.StatisticalMechanics.Code.Universality.HexHWBridgeSubsetBound.Part4
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWEndpointColumns


namespace StatMech.Universality

open HexWalk

open scoped BigOperators

noncomputable section

theorem hlhe_positiveGeom_summable {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (hlhe_positiveGeom r) := by
  apply (summable_geometric_of_lt_one hr0 hr1).of_nonneg_of_le
  · intro T
    simp only [hlhe_positiveGeom]
    split <;> simp_all
  · intro T
    simp only [hlhe_positiveGeom]
    split <;> simp_all

theorem hlhe_activeCriticalMass_nonneg
    (S : Finset HexHWContentHalf) (T : ℕ) :
    0 ≤ hlhe_activeCriticalMass S T := by
  unfold hlhe_activeCriticalMass
  exact Finset.sum_nonneg fun b _ => pow_nonneg hexChiE_pos.le _


theorem hlhe_active_bridge_sum_le_geom
    (S : Finset HexHWContentHalf)
    (hwidth : ∀ b ∈ hhs_activeBridges S, b.width ≤ b.content.length)
    (hmass : ∀ T, hlhe_activeCriticalMass S T ≤ 1)
    {x : ℝ} (hx : 0 ≤ x) (hxchi : x < hexChiE) :
    (∑ b ∈ hhs_activeBridges S, hhc_bridgeWeight x b) ≤
      ∑' T : ℕ, hlhe_positiveGeom (x / hexChiE) T := by
  let A := hhs_activeBridges S
  let r := x / hexChiE
  have hr0 : 0 ≤ r := div_nonneg hx hexChiE_pos.le
  have hr1 : r < 1 := (div_lt_one hexChiE_pos).2 hxchi
  have hterm : ∀ b ∈ A,
      hhc_bridgeWeight x b ≤ r ^ b.width * hhc_bridgeWeight hexChiE b := by
    intro b hb
    exact hexBr_pow_decay x hexChiE b.width b.content.length hx
      hexChiE_pos hxchi.le (hwidth b hb)
  have hgroup :
      (∑ b ∈ A, r ^ b.width * hhc_bridgeWeight hexChiE b) =
        ∑ T ∈ A.image HexBridge.width,
          r ^ T * hlhe_activeCriticalMass S T := by
    calc
      (∑ b ∈ A, r ^ b.width * hhc_bridgeWeight hexChiE b) =
          ∑ T ∈ A.image HexBridge.width,
            ∑ b ∈ A with b.width = T,
              r ^ b.width * hhc_bridgeWeight hexChiE b := by
        symm
        exact Finset.sum_fiberwise_of_maps_to
          (fun b hb => Finset.mem_image_of_mem HexBridge.width hb)
          (fun b => r ^ b.width * hhc_bridgeWeight hexChiE b)
      _ = ∑ T ∈ A.image HexBridge.width,
          r ^ T * hlhe_activeCriticalMass S T := by
        apply Finset.sum_congr rfl
        intro T hT
        unfold hlhe_activeCriticalMass
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        simp only [Finset.mem_filter] at hb
        rw [hb.2]
  have hwidthSum :
      (∑ T ∈ A.image HexBridge.width,
          r ^ T * hlhe_activeCriticalMass S T) ≤
        ∑ T ∈ A.image HexBridge.width, hlhe_positiveGeom r T := by
    apply Finset.sum_le_sum
    intro T hT
    have hTpos : 0 < T := by
      rw [Finset.mem_image] at hT
      obtain ⟨b, _, rfl⟩ := hT
      exact b.width_pos
    rw [hlhe_positiveGeom, if_neg (Nat.ne_of_gt hTpos)]
    exact mul_le_of_le_one_right (pow_nonneg hr0 T) (hmass T)
  have hgeom := hlhe_positiveGeom_summable hr0 hr1
  calc
    (∑ b ∈ hhs_activeBridges S, hhc_bridgeWeight x b) ≤
        ∑ b ∈ A, r ^ b.width * hhc_bridgeWeight hexChiE b :=
      Finset.sum_le_sum hterm
    _ = ∑ T ∈ A.image HexBridge.width,
          r ^ T * hlhe_activeCriticalMass S T := hgroup
    _ ≤ ∑ T ∈ A.image HexBridge.width, hlhe_positiveGeom r T := hwidthSum
    _ ≤ ∑' T : ℕ, hlhe_positiveGeom r T :=
      hgeom.sum_le_tsum _ (fun T _ => by
        unfold hlhe_positiveGeom
        split <;> positivity)


theorem hlhe_half_sum_le_exp_geom
    (S : Finset HexHWContentHalf)
    (hwidth : ∀ b ∈ hhs_activeBridges S, b.width ≤ b.content.length)
    (hmass : ∀ T, hlhe_activeCriticalMass S T ≤ 1)
    {x : ℝ} (hx : 0 ≤ x) (hxchi : x < hexChiE) :
    ∑ s ∈ S, hhc_halfWeight x s ≤
      Real.exp (∑' T : ℕ, hlhe_positiveGeom (x / hexChiE) T) := by
  calc
    ∑ s ∈ S, hhc_halfWeight x s ≤
        Real.exp (∑ b ∈ hhs_activeBridges S, hhc_bridgeWeight x b) :=
      hhs_half_sum_le_exp_bridge_sum S hx
    _ ≤ Real.exp (∑' T : ℕ, hlhe_positiveGeom (x / hexChiE) T) :=
      Real.exp_le_exp.mpr
        (hlhe_active_bridge_sum_le_geom S hwidth hmass hx hxchi)


theorem hlhe_finite_partial_bound_of_critical_masses
    (a : ℂ) (h0 : ℤ) (N : ℕ) {x : ℝ}
    (hx : 0 < x) (hxchi : x < hexChiE)
    (hlower : ∀ T,
      hlhe_activeCriticalMass
        (hlha_augmentedTwoHalfData a h0 N).lowerImage T ≤ 1)
    (hupper : ∀ T,
      hlhe_activeCriticalMass
        (hlha_augmentedTwoHalfData a h0 N).upperImage T ≤ 1) :
    ∑ n ∈ Finset.range N, (hlc_sawCount a h0 n : ℝ) * x ^ n ≤
      (x ^ 2)⁻¹ *
        Real.exp (2 *
          (∑' T : ℕ, hlhe_positiveGeom (x / hexChiE) T)) := by
  let H := hlha_augmentedTwoHalfData a h0 N
  let G := ∑' T : ℕ, hlhe_positiveGeom (x / hexChiE) T
  have hlo : (∑ s ∈ H.lowerImage, hhc_halfWeight x s) ≤ Real.exp G := by
    exact hlhe_half_sum_le_exp_geom H.lowerImage
      (fun b hb => hlhe_lowerActive_width_le_length H hb)
      hlower hx.le hxchi
  have hup : (∑ s ∈ H.upperImage, hhc_halfWeight x s) ≤ Real.exp G := by
    exact hlhe_half_sum_le_exp_geom H.upperImage
      (fun b hb => hlhe_upperActive_width_le_length H hb)
      hupper hx.le hxchi
  calc
    (∑ n ∈ Finset.range N, (hlc_sawCount a h0 n : ℝ) * x ^ n) ≤
        (x ^ 2)⁻¹ *
          ((∑ s ∈ H.lowerImage, hhc_halfWeight x s) *
            (∑ s ∈ H.upperImage, hhc_halfWeight x s)) :=
      hlha_finite_partial_bound a h0 N hx
    _ ≤ (x ^ 2)⁻¹ * (Real.exp G * Real.exp G) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul hlo hup
          (Finset.sum_nonneg fun s _ => hhc_halfWeight_nonneg hx.le s)
          (Real.exp_pos G).le
      · positivity
    _ = (x ^ 2)⁻¹ * Real.exp (2 * G) := by
      rw [← Real.exp_add]
      congr 2
      ring

end
end StatMech.Universality

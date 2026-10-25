/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHWBridgeSubsetBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexContentChoiceBound
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWContent.Part12
import Def.StatisticalMechanics.Code.Universality.HexHWBridgeSubsetBound.Part3


namespace StatMech.Universality

open scoped BigOperators


theorem hhs_encoding_weight
    (S : Finset HexHWContentHalf) (x : ℝ)
    (s : HexHWContentHalf) (hs : s ∈ S) :
    hhc_halfWeight x s =
      ∏ b ∈ (hhs_activeBridges S).attach,
        hhs_boolWeight x b.1 (hhs_bridgeEncoding S s b.1 b.2) := by
  classical
  have hsub : s.1.toFinset ⊆ hhs_activeBridges S := by
    intro b hb
    exact hhs_mem_activeBridges hs (List.mem_toFinset.mp hb)
  rw [hhc_halfWeight]
  rw [← List.prod_toFinset (hhc_bridgeWeight x)
    (strictDecreasingWidths_nodup s.2)]
  simp only [hhs_boolWeight, hhs_bridgeEncoding, decide_eq_true_eq]
  change (∏ b ∈ s.1.toFinset, hhc_bridgeWeight x b) =
    ∏ b ∈ (hhs_activeBridges S).attach,
      if b.1 ∈ s.1 then hhc_bridgeWeight x b.1 else 1
  rw [Finset.prod_attach (hhs_activeBridges S)
    (fun b => if b ∈ s.1 then hhc_bridgeWeight x b else 1)]
  symm
  simp_rw [← List.mem_toFinset]
  rw [Finset.prod_ite_mem]
  rw [Finset.inter_eq_right.mpr hsub]


theorem hhs_half_sum_le_bridge_product
    (S : Finset HexHWContentHalf) {x : ℝ} (hx : 0 ≤ x) :
    ∑ s ∈ S, hhc_halfWeight x s ≤
      ∏ b ∈ hhs_activeBridges S, (1 + hhc_bridgeWeight x b) := by
  classical
  let active := hhs_activeBridges S
  let choices : HexBridge → Finset Bool := fun _ => Finset.univ
  let encode := hhs_bridgeEncoding S
  let choiceWeight := hhs_boolWeight x
  have hbound := finiteChoice_sum_le_prod active choices S encode
    (fun s hs => by simp [choices])
    (hhs_bridgeEncoding_injective S)
    choiceWeight (hhc_halfWeight x)
    (fun s hs => hhs_encoding_weight S x s hs)
    (fun p hp => by
      apply Finset.prod_nonneg
      intro b hb
      cases hq : p b.1 b.2 <;>
        simp [choiceWeight, hhs_boolWeight, hq, hhc_bridgeWeight,
          pow_nonneg hx])
  simpa [active, choices, choiceWeight, hhs_boolWeight, add_comm] using hbound


theorem hhs_half_sum_le_exp_bridge_sum
    (S : Finset HexHWContentHalf) {x : ℝ} (hx : 0 ≤ x) :
    ∑ s ∈ S, hhc_halfWeight x s ≤
      Real.exp (∑ b ∈ hhs_activeBridges S, hhc_bridgeWeight x b) := by
  calc
    ∑ s ∈ S, hhc_halfWeight x s ≤
        ∏ b ∈ hhs_activeBridges S, (1 + hhc_bridgeWeight x b) :=
      hhs_half_sum_le_bridge_product S hx
    _ ≤ ∏ b ∈ hhs_activeBridges S,
        Real.exp (hhc_bridgeWeight x b) := by
      apply Finset.prod_le_prod
      · intro b hb
        exact add_nonneg zero_le_one
          (by exact pow_nonneg hx _)
      · intro b hb
        simpa [add_comm] using Real.add_one_le_exp (hhc_bridgeWeight x b)
    _ = Real.exp (∑ b ∈ hhs_activeBridges S,
        hhc_bridgeWeight x b) := by
      rw [← Real.exp_sum]

end StatMech.Universality

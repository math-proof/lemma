/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWEndpointColumns.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part14
import Theorem.StatisticalMechanics.Code.Universality.HexHWBridgeSubsetBound.Part4


namespace StatMech.Universality

open HexWalk

open scoped BigOperators

noncomputable section

theorem hlhe_coordRun_height_bounds (p d : HexReturnCoord) (ts : List ℤ)
    (hd : d.IsUnit) (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    -((ts.length : ℕ) : ℤ) ≤
        (hlhr_coordRun p d ts).pos.x - (hlhr_coordRun p d ts).pos.y -
          (p.x - p.y) ∧
      (hlhr_coordRun p d ts).pos.x - (hlhr_coordRun p d ts).pos.y -
          (p.x - p.y) ≤ (ts.length : ℕ) := by
  induction ts generalizing p d with
  | nil => simp [hlhr_coordRun]
  | cons t ts ih =>
      have ht := hlegal t (by simp)
      have htail : ∀ u ∈ ts, u = 1 ∨ u = -1 := by
        intro u hu
        exact hlegal u (by simp [hu])
      let e := d.turn t
      have he : e.IsUnit := d.isUnit_turn hd ht
      have hih := ih (p.add e) e he htail
      have hstep : (-1 : ℤ) ≤ e.x - e.y ∧ e.x - e.y ≤ 1 := by
        rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
          rcases ht with rfl | rfl <;>
          simp [e, HexReturnCoord.turn, HexReturnCoord.left,
            HexReturnCoord.right]
      simp only [hlhr_coordRun, List.length_cons, Nat.cast_add, Nat.cast_one]
      change -((ts.length : ℤ) + 1) ≤
          (hlhr_coordRun (p.add e) e ts).pos.x -
              (hlhr_coordRun (p.add e) e ts).pos.y - (p.x - p.y) ∧
        (hlhr_coordRun (p.add e) e ts).pos.x -
              (hlhr_coordRun (p.add e) e ts).pos.y - (p.x - p.y) ≤
          (ts.length : ℤ) + 1
      simp only [HexReturnCoord.add] at hih ⊢
      omega


theorem hlhe_latticeHeight_sub_bounds (ts : List ℤ)
    (hlegal : (ofTurns 0 0 ts).LegalTurns) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ ts.length) :
    -(((j - i : ℕ) : ℤ)) ≤
        hlhr_latticeHeight ts j - hlhr_latticeHeight ts i ∧
      hlhr_latticeHeight ts j - hlhr_latticeHeight ts i ≤
        ((j - i : ℕ) : ℤ) := by
  let r := hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base (ts.take i)
  let seg := (ts.drop i).take (j - i)
  have hi : i ≤ ts.length := le_trans hij hj
  have hsegLegal : ∀ t ∈ seg, t = 1 ∨ t = -1 := by
    intro t ht
    apply hlegal t
    change t ∈ ts
    exact List.mem_of_mem_drop (List.mem_of_mem_take ht)
  have hrunit : r.dir.IsUnit := by
    apply hlha_coordRun_direction_isUnit
    · exact HexReturnCoord.base_isUnit
    · intro t ht
      exact hlegal t (List.mem_of_mem_take ht)
  have hbound := hlhe_coordRun_height_bounds r.pos r.dir seg hrunit hsegLegal
  have htake : ts.take j = ts.take i ++ seg := by
    rw [show j = i + (j - i) by omega, List.take_add]
  have hrun :
      hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base (ts.take j) =
        hlhr_coordRun r.pos r.dir seg := by
    rw [htake, hlha_coordRun_append]
  have hseglen : seg.length = j - i := by
    simp [seg, List.length_take, List.length_drop]
    omega
  unfold hlhr_latticeHeight
  rw [hrun]
  change -(((j - i : ℕ) : ℤ)) ≤
      (hlhr_coordRun r.pos r.dir seg).pos.x -
          (hlhr_coordRun r.pos r.dir seg).pos.y - (r.pos.x - r.pos.y) ∧
    (hlhr_coordRun r.pos r.dir seg).pos.x -
          (hlhr_coordRun r.pos r.dir seg).pos.y - (r.pos.x - r.pos.y) ≤
      ((j - i : ℕ) : ℤ)
  simpa [hseglen] using hbound


theorem hlhe_latticeWidth_le_intervalLength (ts : List ℤ)
    (hlegal : (ofTurns 0 0 ts).LegalTurns) (p : ℕ × ℕ)
    (hp : p.1 ≤ p.2) (hp2 : p.2 ≤ ts.length) :
    hlhr_latticeWidth ts p ≤ (hlhr_intervalContent ts p).length := by
  have hb := hlhe_latticeHeight_sub_bounds ts hlegal hp hp2
  have hlen : (hlhr_intervalContent ts p).length = p.2 - p.1 := by
    unfold hlhr_intervalContent
    rw [List.length_take_of_le]
    simp only [List.length_drop]
    omega
  unfold hlhr_latticeWidth hlhr_latticeDelta
  rw [hlen]
  let delta := hlhr_latticeHeight ts p.2 - hlhr_latticeHeight ts p.1
  by_cases hnonneg : 0 ≤ hlhr_latticeHeight ts p.2 - hlhr_latticeHeight ts p.1
  · have hcast : ((delta.natAbs : ℕ) : ℤ) ≤ ((p.2 - p.1 : ℕ) : ℤ) := by
      rw [Int.natAbs_of_nonneg (by simpa [delta] using hnonneg)]
      simpa [delta] using hb.2
    exact_mod_cast hcast
  · have hnonpos : hlhr_latticeHeight ts p.2 - hlhr_latticeHeight ts p.1 ≤ 0 :=
      le_of_not_ge hnonneg
    have hcast : ((delta.natAbs : ℕ) : ℤ) ≤ ((p.2 - p.1 : ℕ) : ℤ) := by
      rw [Int.ofNat_natAbs_of_nonpos (by simpa [delta] using hnonpos)]
      simpa [delta] using (neg_le_neg hb.1)
    exact_mod_cast hcast


theorem hlhe_literalBridge_width_le_length (ts : List ℤ)
    (hleg : (ofTurns 0 0 ts).IsLegalSAW)
    (hhalf : HLHRLiteralHalfSpace 0 ts)
    (b : HexBridge) (hb : b ∈ hlhr_literalBridgeList ts hleg hhalf) :
    b.width ≤ b.content.length := by
  unfold hlhr_literalBridgeList at hb
  rw [List.mem_map] at hb
  obtain ⟨p, _, rfl⟩ := hb
  apply hlhe_latticeWidth_le_intervalLength ts hleg.1 p.1
  · exact (hlhr_literalInterval_bounds 0 ts hhalf p.1 p.2).1.le
  · exact (hlhr_literalInterval_bounds 0 ts hhalf p.1 p.2).2


theorem hlhe_literalBridge_weight_decay (ts : List ℤ)
    (hleg : (ofTurns 0 0 ts).IsLegalSAW)
    (hhalf : HLHRLiteralHalfSpace 0 ts)
    (b : HexBridge) (hb : b ∈ hlhr_literalBridgeList ts hleg hhalf)
    {x : ℝ} (hx : 0 ≤ x) (hxchi : x ≤ hexChiE) :
    hhc_bridgeWeight x b ≤
      (x / hexChiE) ^ b.width * hhc_bridgeWeight hexChiE b := by
  exact hexBr_pow_decay x hexChiE b.width b.content.length hx hexChiE_pos
    hxchi (hlhe_literalBridge_width_le_length ts hleg hhalf b hb)


theorem hlhe_lowerActive_origin {a : ℂ} {h0 : ℤ} {N : ℕ}
    (H : HLHRAugmentedTwoHalfData a h0 N) {b : HexBridge}
    (hb : b ∈ hhs_activeBridges H.lowerImage) :
    ∃ d : hhc_Dn a h0 N,
      b ∈ hlhr_literalBridgeList (H.lower d)
        (H.lower_legal d) (H.lower_halfSpace d) := by
  classical
  rw [hhs_activeBridges, Finset.mem_biUnion] at hb
  obtain ⟨s, hs, hbs⟩ := hb
  rw [HLHRAugmentedTwoHalfData.lowerImage, Finset.mem_image] at hs
  obtain ⟨d, _, rfl⟩ := hs
  refine ⟨d, ?_⟩
  simpa [HLHRAugmentedTwoHalfData.lowerHalf, hlhr_contentHalf] using
    (List.mem_toFinset.mp hbs)

theorem hlhe_upperActive_origin {a : ℂ} {h0 : ℤ} {N : ℕ}
    (H : HLHRAugmentedTwoHalfData a h0 N) {b : HexBridge}
    (hb : b ∈ hhs_activeBridges H.upperImage) :
    ∃ d : hhc_Dn a h0 N,
      b ∈ hlhr_literalBridgeList (H.upper d)
        (H.upper_legal d) (H.upper_halfSpace d) := by
  classical
  rw [hhs_activeBridges, Finset.mem_biUnion] at hb
  obtain ⟨s, hs, hbs⟩ := hb
  rw [HLHRAugmentedTwoHalfData.upperImage, Finset.mem_image] at hs
  obtain ⟨d, _, rfl⟩ := hs
  refine ⟨d, ?_⟩
  simpa [HLHRAugmentedTwoHalfData.upperHalf, hlhr_contentHalf] using
    (List.mem_toFinset.mp hbs)

theorem hlhe_lowerActive_width_le_length {a : ℂ} {h0 : ℤ} {N : ℕ}
    (H : HLHRAugmentedTwoHalfData a h0 N) {b : HexBridge}
    (hb : b ∈ hhs_activeBridges H.lowerImage) :
    b.width ≤ b.content.length := by
  obtain ⟨d, hbd⟩ := hlhe_lowerActive_origin H hb
  exact hlhe_literalBridge_width_le_length (H.lower d)
    (H.lower_legal d) (H.lower_halfSpace d) b hbd

theorem hlhe_upperActive_width_le_length {a : ℂ} {h0 : ℤ} {N : ℕ}
    (H : HLHRAugmentedTwoHalfData a h0 N) {b : HexBridge}
    (hb : b ∈ hhs_activeBridges H.upperImage) :
    b.width ≤ b.content.length := by
  obtain ⟨d, hbd⟩ := hlhe_upperActive_origin H hb
  exact hlhe_literalBridge_width_le_length (H.upper d)
    (H.upper_legal d) (H.upper_halfSpace d) b hbd

theorem hlhe_lowerActive_weight_decay {a : ℂ} {h0 : ℤ} {N : ℕ}
    (H : HLHRAugmentedTwoHalfData a h0 N) {b : HexBridge}
    (hb : b ∈ hhs_activeBridges H.lowerImage)
    {x : ℝ} (hx : 0 ≤ x) (hxchi : x ≤ hexChiE) :
    hhc_bridgeWeight x b ≤
      (x / hexChiE) ^ b.width * hhc_bridgeWeight hexChiE b :=
  hexBr_pow_decay x hexChiE b.width b.content.length hx hexChiE_pos
    hxchi (hlhe_lowerActive_width_le_length H hb)

theorem hlhe_upperActive_weight_decay {a : ℂ} {h0 : ℤ} {N : ℕ}
    (H : HLHRAugmentedTwoHalfData a h0 N) {b : HexBridge}
    (hb : b ∈ hhs_activeBridges H.upperImage)
    {x : ℝ} (hx : 0 ≤ x) (hxchi : x ≤ hexChiE) :
    hhc_bridgeWeight x b ≤
      (x / hexChiE) ^ b.width * hhc_bridgeWeight hexChiE b :=
  hexBr_pow_decay x hexChiE b.width b.content.length hx hexChiE_pos
    hxchi (hlhe_upperActive_width_le_length H hb)


end
end StatMech.Universality

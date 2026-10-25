/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthTagged.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part26
import Theorem.StatisticalMechanics.Code.Universality.HexTaggedColumnBound
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripColumn.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexContentHalfBound.Part3
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepthTagged.Part4


namespace StatMech.Universality

open HexWalk

open scoped BigOperators

noncomputable section

theorem hlhdt_taggedMajorant_nonneg {x : ℝ} (hx : 0 ≤ x) :
    ∀ T, 0 ≤ hlhdt_taggedMajorant x T := by
  intro T
  unfold hlhdt_taggedMajorant
  split
  · exact le_rfl
  · exact mul_nonneg
      (mul_nonneg (by norm_num) (inv_nonneg.mpr hx))
      (pow_nonneg (div_nonneg hx hexChiE_pos.le) _)

theorem hlhdt_taggedMajorant_summable {x : ℝ}
    (hx : 0 < x) (hxchi : x < hexChiE) :
    Summable (hlhdt_taggedMajorant x) := by
  let r := x / hexChiE
  let K := 8 * x⁻¹
  have hr0 : 0 ≤ r := div_nonneg hx.le hexChiE_pos.le
  have hr1 : r < 1 := (div_lt_one hexChiE_pos).2 hxchi
  have hK : 0 ≤ K := by positivity
  have hgeom : Summable (fun T : ℕ => K * r ^ T) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left K
  apply hgeom.of_nonneg_of_le (hlhdt_taggedMajorant_nonneg hx.le)
  intro T
  unfold hlhdt_taggedMajorant
  split
  · exact mul_nonneg hK (pow_nonneg hr0 _)
  · rfl

theorem hlhdt_bridgeMass_zero
    (S : Finset HexHWContentHalf) (x : ℝ) :
    hchb_bridgeMass S x 0 = 0 := by
  unfold hchb_bridgeMass
  apply Finset.sum_eq_zero
  intro b hb
  simp only [Finset.mem_filter] at hb
  exact (Nat.ne_of_gt b.width_pos hb.2).elim

theorem hlhdt_contentHalfImage_bridgeMass_le_majorant
    (D : Type*) [Fintype D]
    (turns : D → List ℤ)
    (legal : ∀ d, (ofTurns hexAWStart 1 (turns d)).IsLegalSAW)
    (halfSpace : ∀ d, HLHDLiteralHalfSpace (turns d) (legal d))
    {x : ℝ} (hx : 0 < x) (hxone : x ≤ 1) (hxchi : x ≤ hexChiE)
    (hlocal : ∀ T (hT : 0 < T) L, HexCSLocalRelation T L hT)
    (hwindow : ∀ T (hT : 0 < T) L, HexCSBoundaryWindowLaw T L hT) :
    ∀ T,
      hchb_bridgeMass (hlhdt_contentHalfImage D turns legal halfSpace) x T ≤
        hlhdt_taggedMajorant x T := by
  intro T
  cases T with
  | zero =>
      rw [hlhdt_bridgeMass_zero]
      simp [hlhdt_taggedMajorant]
  | succ T =>
      have hT : 0 < T + 1 := by omega
      rw [hlhdt_taggedMajorant, if_neg (Nat.ne_of_gt hT)]
      exact hlhdt_contentHalfImage_bridgeMass_le D turns legal halfSpace
        (T + 1) hT hx hxone hxchi (hlocal (T + 1) hT)
          (hwindow (T + 1) hT)

theorem hlhdt_contentHalfImage_sum_le_tprod
    (D : Type*) [Fintype D]
    (turns : D → List ℤ)
    (legal : ∀ d, (ofTurns hexAWStart 1 (turns d)).IsLegalSAW)
    (halfSpace : ∀ d, HLHDLiteralHalfSpace (turns d) (legal d))
    {x : ℝ} (hx : 0 < x) (hxone : x ≤ 1) (hxchi : x < hexChiE)
    (hlocal : ∀ T (hT : 0 < T) L, HexCSLocalRelation T L hT)
    (hwindow : ∀ T (hT : 0 < T) L, HexCSBoundaryWindowLaw T L hT) :
    ∑ s ∈ hlhdt_contentHalfImage D turns legal halfSpace,
        hhc_halfWeight x s ≤
      ∏' T, (1 + hlhdt_taggedMajorant x T) := by
  exact hchb_sum_halfWeight_le_tprod
    (hlhdt_contentHalfImage D turns legal halfSpace) hx.le
    (hlhdt_taggedMajorant x) (hlhdt_taggedMajorant_nonneg hx.le)
    (hex_bridge_multipliable _ (hlhdt_taggedMajorant_summable hx hxchi))
    (hlhdt_contentHalfImage_bridgeMass_le_majorant D turns legal
      halfSpace hx hxone hxchi.le hlocal hwindow)


end
end StatMech.Universality

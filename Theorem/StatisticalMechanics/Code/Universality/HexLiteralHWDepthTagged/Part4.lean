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
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepthTagged.Part3


namespace StatMech.Universality

open HexWalk

open scoped BigOperators

noncomputable section

theorem hlhdt_fiberCode_decode
    (S : Finset HexHWContentHalf)
    (horigin : ∀ b, b ∈ hchb_bridges S → Nonempty (HLHDBridgeOrigin b))
    (T : ℕ) (hT : 0 < T)
    (b : {b // b ∈ hlhdt_widthFiber S T}) :
    hlhd_decodeColumn (hlhdt_fiberCode S horigin T hT b).1
        (hlhdt_fiberCode S horigin T hT b).2.1 = b.1.content :=
  hlhdt_originCode_decode (hlhdt_pickOrigin S horigin T b) T hT
    (Finset.mem_filter.mp b.2).2

theorem hlhdt_fiberCode_injective
    (S : Finset HexHWContentHalf)
    (horigin : ∀ b, b ∈ hchb_bridges S → Nonempty (HLHDBridgeOrigin b))
    (T : ℕ) (hT : 0 < T) :
    Function.Injective (hlhdt_fiberCode S horigin T hT) := by
  intro b c hcode
  have hcontent := congrArg
    (fun code => hlhd_decodeColumn code.1 code.2.1) hcode
  change hlhd_decodeColumn (hlhdt_fiberCode S horigin T hT b).1
      (hlhdt_fiberCode S horigin T hT b).2.1 =
    hlhd_decodeColumn (hlhdt_fiberCode S horigin T hT c).1
      (hlhdt_fiberCode S horigin T hT c).2.1 at hcontent
  rw [hlhdt_fiberCode_decode S horigin T hT b,
    hlhdt_fiberCode_decode S horigin T hT c] at hcontent
  apply Subtype.ext
  apply hlhdt_bridge_eq_of_width_content
  · exact (Finset.mem_filter.mp b.2).2.trans
      (Finset.mem_filter.mp c.2).2.symm
  · exact hcontent

theorem hlhdt_fiber_raw_weight_le
    (S : Finset HexHWContentHalf)
    (horigin : ∀ b, b ∈ hchb_bridges S → Nonempty (HLHDBridgeOrigin b))
    (T : ℕ) (hT : 0 < T) {x : ℝ} (hx : 0 < x) (hxone : x ≤ 1)
    (b : {b // b ∈ hlhdt_widthFiber S T}) :
    hhc_bridgeWeight x b.1 ≤
      x⁻¹ * x ^ (hlhdt_fiberCode S horigin T hT b).2.1.length := by
  let o := hlhdt_pickOrigin S horigin T b
  have hpow := raw_pow_le_inv_mul_endpoint_pow hx hxone
    (hlhd_intervalRaw o.turns o.interval).length
    (hlhd_intervalEndpoint o.turns o.legal o.halfSpace
      o.interval o.interval_mem).length
    (hlhd_intervalEndpoint_length o.turns o.legal o.halfSpace
      o.interval o.interval_mem)
  have hcontent : b.1.content = hlhd_intervalRaw o.turns o.interval :=
    o.content_eq
  simpa only [hhc_bridgeWeight, hcontent, hlhdt_fiberCode,
    hlhdt_originCode, o] using hpow


theorem hlhdt_bridgeMass_le_eight_inv_colSum
    (S : Finset HexHWContentHalf)
    (horigin : ∀ b, b ∈ hchb_bridges S → Nonempty (HLHDBridgeOrigin b))
    (T : ℕ) (hT : 0 < T) {x : ℝ}
    (hx : 0 < x) (hxone : x ≤ 1) (hxchi : x ≤ hexChiE)
    (hlocal : ∀ L, HexCSLocalRelation T L hT)
    (hwindow : ∀ L, HexCSBoundaryWindowLaw T L hT) :
    hchb_bridgeMass S x T ≤
      8 * x⁻¹ * (hexCSTopColumn T hT hlocal hwindow).colSum x := by
  classical
  let F := hlhdt_widthFiber S T
  let C := hexCSTopColumn T hT hlocal hwindow
  have hcolsum : Summable
      (fun w : {ws : List ℤ // HexCSTopWalkAtWidth T hT ws} =>
        x ^ w.1.length) := by
    have hs := C.colSum_summable (le_of_lt hx) hexChiE_pos hxchi
    simpa only [C, hexCSTopColumn, HexWalk.endpointNumVertices_eq,
      ofTurns_turns] using hs
  have hbound := finiteTagged_sum_le_card_mul_tsum
    (Finset.univ : Finset {b // b ∈ F})
    (hlhdt_fiberCode S horigin T hT)
    (hlhdt_fiberCode_injective S horigin T hT).injOn
    (fun b => hhc_bridgeWeight x b.1)
    (fun w : {ws : List ℤ // HexCSTopWalkAtWidth T hT ws} =>
      x ^ w.1.length)
    x⁻¹ (inv_nonneg.mpr (le_of_lt hx))
    (fun w => pow_nonneg (le_of_lt hx) _)
    hcolsum
    (fun b _ => hlhdt_fiber_raw_weight_le
      S horigin T hT hx hxone b)
  have hcol :
      (∑' w : {ws : List ℤ // HexCSTopWalkAtWidth T hT ws},
          x ^ w.1.length) = C.colSum x := by
    rw [hexCSTopColumn_colSum]
    simp only [HexWalk.endpointNumVertices_eq, ofTurns_turns]
  calc
    hchb_bridgeMass S x T =
        ∑ b : {b // b ∈ F}, hhc_bridgeWeight x b.1 := by
      unfold hchb_bridgeMass
      rw [← Finset.sum_attach, Finset.attach_eq_univ]
      rfl
    _ ≤ x⁻¹ * Fintype.card HLHDColumnTag *
          ∑' w : {ws : List ℤ // HexCSTopWalkAtWidth T hT ws},
            x ^ w.1.length := hbound
    _ = 8 * x⁻¹ * C.colSum x := by
      rw [hlhd_columnTag_card, hcol]
      ring

theorem hlhdt_bridgeMass_le_eight_inv_pow
    (S : Finset HexHWContentHalf)
    (horigin : ∀ b, b ∈ hchb_bridges S → Nonempty (HLHDBridgeOrigin b))
    (T : ℕ) (hT : 0 < T) {x : ℝ}
    (hx : 0 < x) (hxone : x ≤ 1) (hxchi : x ≤ hexChiE)
    (hlocal : ∀ L, HexCSLocalRelation T L hT)
    (hwindow : ∀ L, HexCSBoundaryWindowLaw T L hT) :
    hchb_bridgeMass S x T ≤ 8 * x⁻¹ * (x / hexChiE) ^ T := by
  let C := hexCSTopColumn T hT hlocal hwindow
  calc
    hchb_bridgeMass S x T ≤ 8 * x⁻¹ * C.colSum x :=
      hlhdt_bridgeMass_le_eight_inv_colSum S horigin T hT hx hxone
        hxchi hlocal hwindow
    _ ≤ 8 * x⁻¹ * (x / hexChiE) ^ T := by
      apply mul_le_mul_of_nonneg_left
      · exact C.colSum_le_pow (le_of_lt hx) hexChiE_pos hxchi
      · positivity

theorem hlhdt_contentHalfImage_bridgeMass_le
    (D : Type*) [Fintype D]
    (turns : D → List ℤ)
    (legal : ∀ d, (ofTurns hexAWStart 1 (turns d)).IsLegalSAW)
    (halfSpace : ∀ d, HLHDLiteralHalfSpace (turns d) (legal d))
    (T : ℕ) (hT : 0 < T) {x : ℝ}
    (hx : 0 < x) (hxone : x ≤ 1) (hxchi : x ≤ hexChiE)
    (hlocal : ∀ L, HexCSLocalRelation T L hT)
    (hwindow : ∀ L, HexCSBoundaryWindowLaw T L hT) :
    hchb_bridgeMass (hlhdt_contentHalfImage D turns legal halfSpace) x T ≤
      8 * x⁻¹ * (x / hexChiE) ^ T := by
  exact hlhdt_bridgeMass_le_eight_inv_pow
    (hlhdt_contentHalfImage D turns legal halfSpace)
    (hlhdt_contentHalfImage_origin D turns legal halfSpace)
    T hT hx hxone hxchi hlocal hwindow

end
end StatMech.Universality

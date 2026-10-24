import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexLiteralHWDepthTagged
open StatMech StatMech.Universality StatMech.Universality.HLHDTaggedTwoHalfData


/--
[hlhdt_bridge_eq_of_width_content](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthTagged.lean)
-/
@[path]
private lemma hlhdt_bridge_eq_of_width_content_eq
  {b c : HexBridge}
-- given
  (hwidth : b.width = c.width)
  (hcontent : b.content = c.content) :
-- imply
  b = c := by
-- proof
  apply StatMech.Universality.hlhdt_bridge_eq_of_width_content hwidth hcontent

/--
[HLHDBridgeOrigin.width_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthTagged.lean)
-/
@[path]
private lemma width_eq_eq
  {b : HexBridge}
  {o : HLHDBridgeOrigin b} :
-- imply
  b.width = hlhd_width o.turns o.legal o.interval := by
-- proof
  apply StatMech.Universality.HLHDBridgeOrigin.width_eq o

/--
[HLHDBridgeOrigin.content_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthTagged.lean)
-/
@[path]
private lemma content_eq_eq
  {b : HexBridge}
  {o : HLHDBridgeOrigin b} :
-- imply
  b.content = hlhd_intervalRaw o.turns o.interval := by
-- proof
  apply StatMech.Universality.HLHDBridgeOrigin.content_eq o

/--
[hlhdt_contentHalf_bridge_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthTagged.lean)
-/
@[path]
private lemma hlhdt_contentHalf_bridge_origin_eq
  {ts : List ℤ}
  {b : HexBridge}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hb : b ∈ (hlhd_contentHalf ts hleg hhalf).1) :
-- imply
  Nonempty (HLHDBridgeOrigin b) := by
-- proof
  apply StatMech.Universality.hlhdt_contentHalf_bridge_origin ts hleg hhalf hb

/--
[hlhdt_contentHalfImage_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthTagged.lean)
-/
@[path]
private lemma hlhdt_contentHalfImage_origin_eq
  {D : Type*}
  [Fintype D]
  {turns : D → List ℤ}
  {b : HexBridge}
-- given
  (legal : ∀ d, (ofTurns hexAWStart 1 (turns d)).IsLegalSAW)
  (halfSpace : ∀ d, HLHDLiteralHalfSpace (turns d) (legal d))
  (hb : b ∈ hchb_bridges (hlhdt_contentHalfImage D turns legal halfSpace)) :
-- imply
  Nonempty (HLHDBridgeOrigin b) := by
-- proof
  apply StatMech.Universality.hlhdt_contentHalfImage_origin D turns legal halfSpace b hb

/--
[hlhdt_originCode_decode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthTagged.lean)
-/
@[path]
private lemma hlhdt_originCode_decode_eq
  {b : HexBridge}
  {o : HLHDBridgeOrigin b}
  {T : ℕ}
-- given
  (hT : 0 < T)
  (hbT : b.width = T) :
-- imply
  hlhd_decodeColumn (hlhdt_originCode o T hT hbT).1 (hlhdt_originCode o T hT hbT).2.1 = b.content := by
-- proof
  apply StatMech.Universality.hlhdt_originCode_decode o T hT hbT

/--
[hlhdt_fiberCode_decode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthTagged.lean)
-/
@[path]
private lemma hlhdt_fiberCode_decode_eq
  {S : Finset HexHWContentHalf}
  {T : ℕ}
-- given
  (horigin : ∀ b, b ∈ hchb_bridges S → Nonempty (HLHDBridgeOrigin b))
  (hT : 0 < T)
  (b : {b // b ∈ hlhdt_widthFiber S T}) :
-- imply
  hlhd_decodeColumn (hlhdt_fiberCode S horigin T hT b).1 (hlhdt_fiberCode S horigin T hT b).2.1 = b.1.content := by
-- proof
  apply StatMech.Universality.hlhdt_fiberCode_decode S horigin T hT b

/--
[hlhdt_fiberCode_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthTagged.lean)
-/
@[path]
private lemma hlhdt_fiberCode_injective_eq
  {S : Finset HexHWContentHalf}
  {T : ℕ}
-- given
  (horigin : ∀ b, b ∈ hchb_bridges S → Nonempty (HLHDBridgeOrigin b))
  (hT : 0 < T) :
-- imply
  Function.Injective (hlhdt_fiberCode S horigin T hT) := by
-- proof
  apply StatMech.Universality.hlhdt_fiberCode_injective S horigin T hT

/--
[hlhdt_fiber_raw_weight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthTagged.lean)
-/
@[path]
private lemma hlhdt_fiber_raw_weight_le_eq
  {S : Finset HexHWContentHalf}
  {T : ℕ}
  {x : ℝ}
-- given
  (horigin : ∀ b, b ∈ hchb_bridges S → Nonempty (HLHDBridgeOrigin b))
  (hT : 0 < T)
  (hx : 0 < x)
  (hxone : x ≤ 1)
  (b : {b // b ∈ hlhdt_widthFiber S T}) :
-- imply
  hhc_bridgeWeight x b.1 ≤ x⁻¹ * x ^ (hlhdt_fiberCode S horigin T hT b).2.1.length := by
-- proof
  apply StatMech.Universality.hlhdt_fiber_raw_weight_le S horigin T hT hx hxone b

/--
[hlhdt_bridgeMass_le_eight_inv_colSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthTagged.lean)
-/
@[path]
private lemma hlhdt_bridgeMass_le_eight_inv_colSum_eq
  {S : Finset HexHWContentHalf}
  {T : ℕ}
  {x : ℝ}
-- given
  (horigin : ∀ b, b ∈ hchb_bridges S → Nonempty (HLHDBridgeOrigin b))
  (hT : 0 < T)
  (hx : 0 < x)
  (hxone : x ≤ 1)
  (hxchi : x ≤ hexChiE)
  (hlocal : ∀ L, HexCSLocalRelation T L hT)
  (hwindow : ∀ L, HexCSBoundaryWindowLaw T L hT) :
-- imply
  hchb_bridgeMass S x T ≤ 8 * x⁻¹ * (hexCSTopColumn T hT hlocal hwindow).colSum x := by
-- proof
  apply StatMech.Universality.hlhdt_bridgeMass_le_eight_inv_colSum S horigin T hT hx hxone hxchi hlocal hwindow

/--
[hlhdt_bridgeMass_le_eight_inv_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthTagged.lean)
-/
@[path]
private lemma hlhdt_bridgeMass_le_eight_inv_pow_eq
  {S : Finset HexHWContentHalf}
  {T : ℕ}
  {x : ℝ}
-- given
  (horigin : ∀ b, b ∈ hchb_bridges S → Nonempty (HLHDBridgeOrigin b))
  (hT : 0 < T)
  (hx : 0 < x)
  (hxone : x ≤ 1)
  (hxchi : x ≤ hexChiE)
  (hlocal : ∀ L, HexCSLocalRelation T L hT)
  (hwindow : ∀ L, HexCSBoundaryWindowLaw T L hT) :
-- imply
  hchb_bridgeMass S x T ≤ 8 * x⁻¹ * (x / hexChiE) ^ T := by
-- proof
  apply StatMech.Universality.hlhdt_bridgeMass_le_eight_inv_pow S horigin T hT hx hxone hxchi hlocal hwindow

/--
[hlhdt_contentHalfImage_bridgeMass_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthTagged.lean)
-/
@[path]
private lemma hlhdt_contentHalfImage_bridgeMass_le_eq
  {D : Type*}
  [Fintype D]
  {turns : D → List ℤ}
  {T : ℕ}
  {x : ℝ}
-- given
  (legal : ∀ d, (ofTurns hexAWStart 1 (turns d)).IsLegalSAW)
  (halfSpace : ∀ d, HLHDLiteralHalfSpace (turns d) (legal d))
  (hT : 0 < T)
  (hx : 0 < x)
  (hxone : x ≤ 1)
  (hxchi : x ≤ hexChiE)
  (hlocal : ∀ L, HexCSLocalRelation T L hT)
  (hwindow : ∀ L, HexCSBoundaryWindowLaw T L hT) :
-- imply
  hchb_bridgeMass (hlhdt_contentHalfImage D turns legal halfSpace) x T ≤ 8 * x⁻¹ * (x / hexChiE) ^ T := by
-- proof
  apply StatMech.Universality.hlhdt_contentHalfImage_bridgeMass_le D turns legal halfSpace T hT hx hxone hxchi hlocal hwindow

/--
[hlhdt_taggedMajorant_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthTagged.lean)
-/
@[path]
private lemma hlhdt_taggedMajorant_nonneg_eq
  {x : ℝ}
-- given
  (hx : 0 ≤ x) :
-- imply
  ∀ T, 0 ≤ hlhdt_taggedMajorant x T := by
-- proof
  apply StatMech.Universality.hlhdt_taggedMajorant_nonneg hx

/--
[hlhdt_taggedMajorant_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthTagged.lean)
-/
@[path]
private lemma hlhdt_taggedMajorant_summable_eq
  {x : ℝ}
-- given
  (hx : 0 < x)
  (hxchi : x < hexChiE) :
-- imply
  Summable (hlhdt_taggedMajorant x) := by
-- proof
  apply StatMech.Universality.hlhdt_taggedMajorant_summable hx hxchi

/--
[hlhdt_bridgeMass_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthTagged.lean)
-/
@[path]
private lemma hlhdt_bridgeMass_zero_eq
  {S : Finset HexHWContentHalf}
  {x : ℝ} :
-- imply
  hchb_bridgeMass S x 0 = 0 := by
-- proof
  apply StatMech.Universality.hlhdt_bridgeMass_zero S x

/--
[hlhdt_contentHalfImage_bridgeMass_le_majorant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthTagged.lean)
-/
@[path]
private lemma hlhdt_contentHalfImage_bridgeMass_le_majorant_eq
  {D : Type*}
  [Fintype D]
  {turns : D → List ℤ}
  {x : ℝ}
-- given
  (legal : ∀ d, (ofTurns hexAWStart 1 (turns d)).IsLegalSAW)
  (halfSpace : ∀ d, HLHDLiteralHalfSpace (turns d) (legal d))
  (hx : 0 < x)
  (hxone : x ≤ 1)
  (hxchi : x ≤ hexChiE)
  (hlocal : ∀ T (hT : 0 < T) L, HexCSLocalRelation T L hT)
  (hwindow : ∀ T (hT : 0 < T) L, HexCSBoundaryWindowLaw T L hT) :
-- imply
  ∀ T, hchb_bridgeMass (hlhdt_contentHalfImage D turns legal halfSpace) x T ≤ hlhdt_taggedMajorant x T := by
-- proof
  apply StatMech.Universality.hlhdt_contentHalfImage_bridgeMass_le_majorant D turns legal halfSpace hx hxone hxchi hlocal hwindow

/--
[hlhdt_contentHalfImage_sum_le_tprod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthTagged.lean)
-/
@[path]
private lemma hlhdt_contentHalfImage_sum_le_tprod_eq
  {D : Type*}
  [Fintype D]
  {turns : D → List ℤ}
  {x : ℝ}
-- given
  (legal : ∀ d, (ofTurns hexAWStart 1 (turns d)).IsLegalSAW)
  (halfSpace : ∀ d, HLHDLiteralHalfSpace (turns d) (legal d))
  (hx : 0 < x)
  (hxone : x ≤ 1)
  (hxchi : x < hexChiE)
  (hlocal : ∀ T (hT : 0 < T) L, HexCSLocalRelation T L hT)
  (hwindow : ∀ T (hT : 0 < T) L, HexCSBoundaryWindowLaw T L hT) :
-- imply
  ∑ s ∈ hlhdt_contentHalfImage D turns legal halfSpace, hhc_halfWeight x s ≤ ∏' T, (1 + hlhdt_taggedMajorant x T) := by
-- proof
  apply StatMech.Universality.hlhdt_contentHalfImage_sum_le_tprod D turns legal halfSpace hx hxone hxchi hlocal hwindow

/--
[lowerHalf_turns](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthTagged.lean)
-/
@[path]
private lemma lowerHalf_turns_eq
  {a : ℂ}
  {h0 : ℤ}
  {N extra : ℕ}
  {H : HLHDTaggedTwoHalfData a h0 N extra}
  {d : hhc_Dn a h0 N} :
-- imply
  hhc_halfTurns (H.lowerHalf d) = H.lower d := by
-- proof
  apply StatMech.Universality.HLHDTaggedTwoHalfData.lowerHalf_turns H d

/--
[upperHalf_turns](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthTagged.lean)
-/
@[path]
private lemma upperHalf_turns_eq
  {a : ℂ}
  {h0 : ℤ}
  {N extra : ℕ}
  {H : HLHDTaggedTwoHalfData a h0 N extra}
  {d : hhc_Dn a h0 N} :
-- imply
  hhc_halfTurns (H.upperHalf d) = H.upper d := by
-- proof
  apply StatMech.Universality.HLHDTaggedTwoHalfData.upperHalf_turns H d

/--
[contentPair_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthTagged.lean)
-/
@[path]
private lemma contentPair_injective_eq
  {a : ℂ}
  {h0 : ℤ}
  {N extra : ℕ}
  {H : HLHDTaggedTwoHalfData a h0 N extra} :
-- imply
  Function.Injective H.contentPair := by
-- proof
  apply StatMech.Universality.HLHDTaggedTwoHalfData.contentPair_injective H

/--
[source_weight_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthTagged.lean)
-/
@[path]
private lemma source_weight_factor_eq
  {a : ℂ}
  {h0 : ℤ}
  {N extra : ℕ}
  {H : HLHDTaggedTwoHalfData a h0 N extra}
  {x : ℝ}
  {d : hhc_Dn a h0 N}
-- given
  (hx : 0 < x) :
-- imply
  x ^ d.1.length = (x ^ extra)⁻¹ * (hhc_halfWeight x (H.lowerHalf d) * hhc_halfWeight x (H.upperHalf d)) := by
-- proof
  apply StatMech.Universality.HLHDTaggedTwoHalfData.source_weight_factor H x hx d

/--
[sum_eq_pairImage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthTagged.lean)
-/
@[path]
private lemma sum_eq_pairImage_eq
  {a : ℂ}
  {h0 : ℤ}
  {N extra : ℕ}
  {H : HLHDTaggedTwoHalfData a h0 N extra}
  {x : ℝ} :
-- imply
  ∑ d : hhc_Dn a h0 N, hhc_halfWeight x (H.lowerHalf d) * hhc_halfWeight x (H.upperHalf d) = ∑ p ∈ H.pairImage, hhc_halfWeight x p.1 * hhc_halfWeight x p.2 := by
-- proof
  apply StatMech.Universality.HLHDTaggedTwoHalfData.sum_eq_pairImage H x

/--
[pairImage_subset_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthTagged.lean)
-/
@[path]
private lemma pairImage_subset_product_eq
  {a : ℂ}
  {h0 : ℤ}
  {N extra : ℕ}
  {H : HLHDTaggedTwoHalfData a h0 N extra} :
-- imply
  H.pairImage ⊆ H.lowerImage ×ˢ H.upperImage := by
-- proof
  apply StatMech.Universality.HLHDTaggedTwoHalfData.pairImage_subset_product H

/--
[pair_sum_le_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthTagged.lean)
-/
@[path]
private lemma pair_sum_le_product_eq
  {a : ℂ}
  {h0 : ℤ}
  {N extra : ℕ}
  {H : HLHDTaggedTwoHalfData a h0 N extra}
  {x : ℝ}
-- given
  (hx : 0 ≤ x) :
-- imply
  (∑ p ∈ H.pairImage, hhc_halfWeight x p.1 * hhc_halfWeight x p.2) ≤ (∑ s ∈ H.lowerImage, hhc_halfWeight x s) * (∑ s ∈ H.upperImage, hhc_halfWeight x s) := by
-- proof
  apply StatMech.Universality.HLHDTaggedTwoHalfData.pair_sum_le_product H hx

/--
[finite_partial_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthTagged.lean)
-/
@[path]
private lemma finite_partial_bound_eq
  {a : ℂ}
  {h0 : ℤ}
  {N extra : ℕ}
  {H : HLHDTaggedTwoHalfData a h0 N extra}
  {x : ℝ}
-- given
  (hx : 0 < x) :
-- imply
  ∑ n ∈ Finset.range N, (hlc_sawCount a h0 n : ℝ) * x ^ n ≤ (x ^ extra)⁻¹ * ((∑ s ∈ H.lowerImage, hhc_halfWeight x s) * (∑ s ∈ H.upperImage, hhc_halfWeight x s)) := by
-- proof
  apply StatMech.Universality.HLHDTaggedTwoHalfData.finite_partial_bound H hx

/--
[finite_partial_bound_tagged](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthTagged.lean)
-/
@[path]
private lemma finite_partial_bound_tagged_eq
  {a : ℂ}
  {h0 : ℤ}
  {N extra : ℕ}
  {H : HLHDTaggedTwoHalfData a h0 N extra}
  {x : ℝ}
-- given
  (hx : 0 < x)
  (hxone : x ≤ 1)
  (hxchi : x < hexChiE)
  (hlocal : ∀ T (hT : 0 < T) L, HexCSLocalRelation T L hT)
  (hwindow : ∀ T (hT : 0 < T) L, HexCSBoundaryWindowLaw T L hT) :
-- imply
  ∑ n ∈ Finset.range N, (hlc_sawCount a h0 n : ℝ) * x ^ n ≤ (x ^ extra)⁻¹ * (∏' T, (1 + hlhdt_taggedMajorant x T)) ^ 2 := by
-- proof
  apply StatMech.Universality.HLHDTaggedTwoHalfData.finite_partial_bound_tagged H hx hxone hxchi hlocal hwindow

/--
[summable_of_taggedTwoHalfData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthTagged.lean)
-/
@[path]
private lemma summable_of_taggedTwoHalfData_eq
  {a : ℂ}
  {h0 : ℤ}
  {N extra : ℕ}
  {x : ℝ}
-- given
  (H : ∀ N, HLHDTaggedTwoHalfData a h0 N extra)
  (hx : 0 < x)
  (hxone : x ≤ 1)
  (hxchi : x < hexChiE)
  (hlocal : ∀ T (hT : 0 < T) L, HexCSLocalRelation T L hT)
  (hwindow : ∀ T (hT : 0 < T) L, HexCSBoundaryWindowLaw T L hT) :
-- imply
  Summable (fun n => hlc_sawCountR a h0 n * x ^ n) := by
-- proof
  apply StatMech.Universality.HLHDTaggedTwoHalfData.summable_of_taggedTwoHalfData H hx hxone hxchi hlocal hwindow


-- created on 2026-10-23

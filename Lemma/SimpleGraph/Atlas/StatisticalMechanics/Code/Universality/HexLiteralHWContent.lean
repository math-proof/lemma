import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWContent.Part12
open StatMech StatMech.Universality StatMech.Universality.HexHWContentDecomp


/--
[hhc_widthList_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWContent.lean)
-/
@[path]
private lemma hhc_widthList_nodup_eq
  {s : HexHWContentHalf} :
-- imply
  (s.1.map HexBridge.width).Nodup := by
-- proof
  apply StatMech.Universality.hhc_widthList_nodup s

/--
[hhc_card_widths](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWContent.lean)
-/
@[path]
private lemma hhc_card_widths_eq
  {s : HexHWContentHalf} :
-- imply
  (hhc_widths s).card = s.1.length := by
-- proof
  apply StatMech.Universality.hhc_card_widths s

/--
[hhc_width_projection_not_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWContent.lean)
-/
@[path]
private lemma hhc_width_projection_not_injective_eq :
-- imply
  ¬ Function.Injective hhc_widths := by
-- proof
  apply StatMech.Universality.hhc_width_projection_not_injective

/--
[hhc_sum_grouped_by_widths](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWContent.lean)
-/
@[path]
private lemma hhc_sum_grouped_by_widths_eq
  {S : Finset HexHWContentHalf}
  {w : HexHWContentHalf → ℝ} :
-- imply
  ∑ s ∈ S, w s = ∑ widths ∈ S.image hhc_widths, ∑ s ∈ S with hhc_widths s = widths, w s := by
-- proof
  apply StatMech.Universality.hhc_sum_grouped_by_widths S w

/--
[hhc_halfWeight_eq_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWContent.lean)
-/
@[path]
private lemma hhc_halfWeight_eq_pow_eq
  {x : ℝ}
  {s : HexHWContentHalf} :
-- imply
  hhc_halfWeight x s = x ^ (hhc_halfTurns s).length := by
-- proof
  apply StatMech.Universality.hhc_halfWeight_eq_pow x s

/--
[hhc_halfWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWContent.lean)
-/
@[path]
private lemma hhc_halfWeight_nonneg_eq
  {x : ℝ}
  {s : HexHWContentHalf}
-- given
  (hx : 0 ≤ x) :
-- imply
  0 ≤ hhc_halfWeight x s := by
-- proof
  apply StatMech.Universality.hhc_halfWeight_nonneg hx s

/--
[pair_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWContent.lean)
-/
@[path]
private lemma pair_injective_eq
  {D : Type}
  {H : HexHWContentDecomp D} :
-- imply
  Function.Injective H.pair := by
-- proof
  apply StatMech.Universality.HexHWContentDecomp.pair_injective H

/--
[weight_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWContent.lean)
-/
@[path]
private lemma weight_factor_eq
  {D : Type}
  {H : HexHWContentDecomp D}
  {x : ℝ}
  {d : D} :
-- imply
  x ^ (H.turns d).length = hhc_halfWeight x (H.lower d) * hhc_halfWeight x (H.upper d) := by
-- proof
  apply StatMech.Universality.HexHWContentDecomp.weight_factor H x d

/--
[sum_eq_pairImage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWContent.lean)
-/
@[path]
private lemma sum_eq_pairImage_eq
  {D : Type}
  [Fintype D]
  {H : HexHWContentDecomp D}
  {x : ℝ} :
-- imply
  ∑ d : D, x ^ (H.turns d).length = ∑ p ∈ H.pairImage, hhc_halfWeight x p.1 * hhc_halfWeight x p.2 := by
-- proof
  apply StatMech.Universality.HexHWContentDecomp.sum_eq_pairImage H x

/--
[pairImage_subset_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWContent.lean)
-/
@[path]
private lemma pairImage_subset_product_eq
  {D : Type}
  [Fintype D]
  {H : HexHWContentDecomp D} :
-- imply
  H.pairImage ⊆ H.lowerImage ×ˢ H.upperImage := by
-- proof
  apply StatMech.Universality.HexHWContentDecomp.pairImage_subset_product H

/--
[finite_content_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWContent.lean)
-/
@[path]
private lemma finite_content_bound_eq
  {D : Type}
  [Fintype D]
  {H : HexHWContentDecomp D}
  {x : ℝ}
-- given
  (hx : 0 ≤ x) :
-- imply
  ∑ d : D, x ^ (H.turns d).length ≤ (∑ s ∈ H.lowerImage, hhc_halfWeight x s) * (∑ s ∈ H.upperImage, hhc_halfWeight x s) := by
-- proof
  apply StatMech.Universality.HexHWContentDecomp.finite_content_bound H hx

/--
[hhc_Dn_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWContent.lean)
-/
@[path]
private lemma hhc_Dn_spec_eq
  {a : ℂ}
  {N : ℕ}
  {d : hhc_Dn a h0 N}
-- given
  (h0 : ℤ) :
-- imply
  (ofTurns a h0 d.1).IsLegalSAW ∧ d.1.length < N := by
-- proof
  apply StatMech.Universality.hhc_Dn_spec a h0 N d

/--
[hhc_partial_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWContent.lean)
-/
@[path]
private lemma hhc_partial_eq_eq
  {a : ℂ}
  {x : ℝ}
  {N : ℕ}
-- given
  (h0 : ℤ) :
-- imply
  ∑ d : hhc_Dn a h0 N, x ^ d.1.length = ∑ n ∈ Finset.range N, (hlc_sawCount a h0 n : ℝ) * x ^ n := by
-- proof
  apply StatMech.Universality.hhc_partial_eq a h0 x N

/--
[hhc_literal_partial_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWContent.lean)
-/
@[path]
private lemma hhc_literal_partial_bound_eq
  {a : ℂ}
  {N : ℕ}
  {lower upper : hhc_Dn a h0 N → HexHWContentHalf}
  {x : ℝ}
-- given
  (h0 : ℤ)
  (hreconstruct : ∀ d, d.1 = hhc_halfTurns (lower d) ++ hhc_halfTurns (upper d))
  (hx : 0 ≤ x) :
-- imply
  ∑ n ∈ Finset.range N, (hlc_sawCount a h0 n : ℝ) * x ^ n ≤ (∑ s ∈ (hhc_literalDecomp a h0 N lower upper hreconstruct).lowerImage, hhc_halfWeight x s) * (∑ s ∈ (hhc_literalDecomp a h0 N lower upper hreconstruct).upperImage, hhc_halfWeight x s) := by
-- proof
  apply StatMech.Universality.hhc_literal_partial_bound a h0 N lower upper hreconstruct hx

/--
[hhc_bridgeOfNonempty_width](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWContent.lean)
-/
@[path]
private lemma hhc_bridgeOfNonempty_width_eq
  {ts : List ℤ}
-- given
  (hne : ts ≠ []) :
-- imply
  (hhc_bridgeOfNonempty ts hne).width = ts.length := by
-- proof
  apply StatMech.Universality.hhc_bridgeOfNonempty_width ts hne

/--
[hhc_bridgeOfNonempty_content](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWContent.lean)
-/
@[path]
private lemma hhc_bridgeOfNonempty_content_eq
  {ts : List ℤ}
-- given
  (hne : ts ≠ []) :
-- imply
  (hhc_bridgeOfNonempty ts hne).content = ts := by
-- proof
  apply StatMech.Universality.hhc_bridgeOfNonempty_content ts hne

/--
[hhc_halfTurns_halfOfList](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWContent.lean)
-/
@[path]
private lemma hhc_halfTurns_halfOfList_eq
  {ts : List ℤ} :
-- imply
  hhc_halfTurns (hhc_halfOfList ts) = ts := by
-- proof
  apply StatMech.Universality.hhc_halfTurns_halfOfList ts

/--
[hhc_halfOfList_strict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWContent.lean)
-/
@[path]
private lemma hhc_halfOfList_strict_eq
  {ts : List ℤ} :
-- imply
  StrictDecreasingWidths (hhc_halfOfList ts).1 := by
-- proof
  apply StatMech.Universality.hhc_halfOfList_strict ts

/--
[hhc_bridge_decomp_retains_turns](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWContent.lean)
-/
@[path]
private lemma hhc_bridge_decomp_retains_turns_eq
  {s : HexHWContentHalf} :
-- imply
  (hexHW_bridge_decomp s : List (ℕ × ℤ)).map Prod.snd = hhc_halfTurns s := by
-- proof
  apply StatMech.Universality.hhc_bridge_decomp_retains_turns s

/--
[hhc_literalLower_turns](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWContent.lean)
-/
@[path]
private lemma hhc_literalLower_turns_eq
  {a : ℂ}
  {N : ℕ}
  {d : hhc_Dn a h0 N}
-- given
  (h0 : ℤ) :
-- imply
  hhc_halfTurns (hhc_literalLower a h0 N d) = d.1.take (hexW2_cutPos h0 d.1) := by
-- proof
  apply StatMech.Universality.hhc_literalLower_turns a h0 N d

/--
[hhc_literalUpper_turns](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWContent.lean)
-/
@[path]
private lemma hhc_literalUpper_turns_eq
  {a : ℂ}
  {N : ℕ}
  {d : hhc_Dn a h0 N}
-- given
  (h0 : ℤ) :
-- imply
  hhc_halfTurns (hhc_literalUpper a h0 N d) = d.1.drop (hexW2_cutPos h0 d.1) := by
-- proof
  apply StatMech.Universality.hhc_literalUpper_turns a h0 N d

/--
[hhc_literalHighest_reconstruct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWContent.lean)
-/
@[path]
private lemma hhc_literalHighest_reconstruct_eq
  {a : ℂ}
  {N : ℕ}
  {d : hhc_Dn a h0 N}
-- given
  (h0 : ℤ) :
-- imply
  d.1 = hhc_halfTurns (hhc_literalLower a h0 N d) ++ hhc_halfTurns (hhc_literalUpper a h0 N d) := by
-- proof
  apply StatMech.Universality.hhc_literalHighest_reconstruct a h0 N d

/--
[hhc_literalHighest_bridgeDecomp_reconstruct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWContent.lean)
-/
@[path]
private lemma hhc_literalHighest_bridgeDecomp_reconstruct_eq
  {a : ℂ}
  {N : ℕ}
  {d : hhc_Dn a h0 N}
-- given
  (h0 : ℤ) :
-- imply
  d.1 = (hexHW_bridge_decomp (hhc_literalLower a h0 N d) : List (ℕ × ℤ)).map Prod.snd ++ (hexHW_bridge_decomp (hhc_literalUpper a h0 N d) : List (ℕ × ℤ)).map Prod.snd := by
-- proof
  apply StatMech.Universality.hhc_literalHighest_bridgeDecomp_reconstruct a h0 N d

/--
[hhc_literalHighest_cut_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWContent.lean)
-/
@[path]
private lemma hhc_literalHighest_cut_spec_eq
  {a : ℂ}
  {N : ℕ}
  {d : hhc_Dn a h0 N}
-- given
  (h0 : ℤ) :
-- imply
  hexW2_cutPos h0 d.1 ≤ d.1.length ∧ (∀ k ≤ d.1.length, hexW2_partialDisp h0 d.1 k ≤ hexW2_partialDisp h0 d.1 (hexW2_cutPos h0 d.1)) ∧ (∀ k, k < hexW2_cutPos h0 d.1 → hexW2_partialDisp h0 d.1 k < hexW2_partialDisp h0 d.1 (hexW2_cutPos h0 d.1)) := by
-- proof
  apply StatMech.Universality.hhc_literalHighest_cut_spec a h0 N d

/--
[hhc_literalHighest_halves_legal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWContent.lean)
-/
@[path]
private lemma hhc_literalHighest_halves_legal_eq
  {a : ℂ}
  {N : ℕ}
  {d : hhc_Dn a h0 N}
-- given
  (h0 : ℤ) :
-- imply
  (ofTurns a h0 (hhc_halfTurns (hhc_literalLower a h0 N d))).IsLegalSAW ∧ (ofTurns (hexDropMid a h0 d.1 (hexW2_cutPos h0 d.1)) (h0 + (d.1.take (hexW2_cutPos h0 d.1)).sum) (hhc_halfTurns (hhc_literalUpper a h0 N d))).IsLegalSAW := by
-- proof
  apply StatMech.Universality.hhc_literalHighest_halves_legal a h0 N d

/--
[hhc_literalHighest_partial_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWContent.lean)
-/
@[path]
private lemma hhc_literalHighest_partial_bound_eq
  {a : ℂ}
  {N : ℕ}
  {x : ℝ}
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x) :
-- imply
  ∑ n ∈ Finset.range N, (hlc_sawCount a h0 n : ℝ) * x ^ n ≤ (∑ s ∈ (hhc_literalHighestDecomp a h0 N).lowerImage, hhc_halfWeight x s) * (∑ s ∈ (hhc_literalHighestDecomp a h0 N).upperImage, hhc_halfWeight x s) := by
-- proof
  apply StatMech.Universality.hhc_literalHighest_partial_bound a h0 N hx

/--
[hhc_retagBridge_width](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWContent.lean)
-/
@[path]
private lemma hhc_retagBridge_width_eq
  {b : HexBridge}
  {T : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  (hhc_retagBridge b T hT).width = T := by
-- proof
  apply StatMech.Universality.hhc_retagBridge_width b T hT

/--
[hhc_retagBridge_content](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWContent.lean)
-/
@[path]
private lemma hhc_retagBridge_content_eq
  {b : HexBridge}
  {T : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  (hhc_retagBridge b T hT).content = b.content := by
-- proof
  apply StatMech.Universality.hhc_retagBridge_content b T hT

/--
[hhc_same_content_distinct_widths](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWContent.lean)
-/
@[path]
private lemma hhc_same_content_distinct_widths_eq
  {b : HexBridge} :
-- imply
  ∃ b₁ b₂ : HexBridge, b₁.content = b₂.content ∧ b₁.width ≠ b₂.width := by
-- proof
  apply StatMech.Universality.hhc_same_content_distinct_widths b


-- created on 2026-10-23

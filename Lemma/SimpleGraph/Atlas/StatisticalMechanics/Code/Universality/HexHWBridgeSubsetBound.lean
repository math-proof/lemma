import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexHWBridgeSubsetBound.Part4
open StatMech StatMech.Universality


/--
[strictDecreasingWidths_eq_of_mem_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHWBridgeSubsetBound.lean)
-/
@[path]
private lemma strictDecreasingWidths_eq_of_mem_iff_eq
  {xs ys : List HexBridge}
-- given
  (hx : StrictDecreasingWidths xs)
  (hy : StrictDecreasingWidths ys)
  (hmem : ∀ b, b ∈ xs ↔ b ∈ ys) :
-- imply
  xs = ys := by
-- proof
  apply StatMech.Universality.strictDecreasingWidths_eq_of_mem_iff hx hy hmem

/--
[strictDecreasingWidths_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHWBridgeSubsetBound.lean)
-/
@[path]
private lemma strictDecreasingWidths_nodup_eq
  {bs : List HexBridge}
-- given
  (hbs : StrictDecreasingWidths bs) :
-- imply
  bs.Nodup := by
-- proof
  apply StatMech.Universality.strictDecreasingWidths_nodup hbs

/--
[hhs_mem_activeBridges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHWBridgeSubsetBound.lean)
-/
@[path]
private lemma hhs_mem_activeBridges_eq
  {S : Finset HexHWContentHalf}
  {s : HexHWContentHalf}
  {b : HexBridge}
-- given
  (hs : s ∈ S)
  (hb : b ∈ s.1) :
-- imply
  b ∈ hhs_activeBridges S := by
-- proof
  apply StatMech.Universality.hhs_mem_activeBridges hs hb

/--
[hhs_bridgeEncoding_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHWBridgeSubsetBound.lean)
-/
@[path]
private lemma hhs_bridgeEncoding_injective_eq
  {S : Finset HexHWContentHalf} :
-- imply
  Set.InjOn (hhs_bridgeEncoding S) (S : Set HexHWContentHalf) := by
-- proof
  apply StatMech.Universality.hhs_bridgeEncoding_injective S

/--
[hhs_encoding_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHWBridgeSubsetBound.lean)
-/
@[path]
private lemma hhs_encoding_weight_eq
  {S : Finset HexHWContentHalf}
  {x : ℝ}
  {s : HexHWContentHalf}
-- given
  (hs : s ∈ S) :
-- imply
  hhc_halfWeight x s = ∏ b ∈ (hhs_activeBridges S).attach, hhs_boolWeight x b.1 (hhs_bridgeEncoding S s b.1 b.2) := by
-- proof
  apply StatMech.Universality.hhs_encoding_weight S x s hs

/--
[hhs_half_sum_le_bridge_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHWBridgeSubsetBound.lean)
-/
@[path]
private lemma hhs_half_sum_le_bridge_product_eq
  {S : Finset HexHWContentHalf}
  {x : ℝ}
-- given
  (hx : 0 ≤ x) :
-- imply
  ∑ s ∈ S, hhc_halfWeight x s ≤ ∏ b ∈ hhs_activeBridges S, (1 + hhc_bridgeWeight x b) := by
-- proof
  apply StatMech.Universality.hhs_half_sum_le_bridge_product S hx

/--
[hhs_half_sum_le_exp_bridge_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHWBridgeSubsetBound.lean)
-/
@[path]
private lemma hhs_half_sum_le_exp_bridge_sum_eq
  {S : Finset HexHWContentHalf}
  {x : ℝ}
-- given
  (hx : 0 ≤ x) :
-- imply
  ∑ s ∈ S, hhc_halfWeight x s ≤ Real.exp (∑ b ∈ hhs_activeBridges S, hhc_bridgeWeight x b) := by
-- proof
  apply StatMech.Universality.hhs_half_sum_le_exp_bridge_sum S hx


-- created on 2026-10-23

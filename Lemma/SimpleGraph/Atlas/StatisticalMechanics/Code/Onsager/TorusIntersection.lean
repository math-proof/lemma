import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part8
open StatMech StatMech.Onsager


/--
[ons_edgeBit_eq_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_edgeBit_eq_one_iff_eq
  [DecidableEq V]
  {F : Finset (Sym2 V)}
  {e : Sym2 V} :
-- imply
  ons_edgeBit F e = 1 ↔ e ∈ F := by
-- proof
  apply StatMech.Onsager.ons_edgeBit_eq_one_iff F e

/--
[ons_edgeBit_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_edgeBit_eq_zero_iff_eq
  [DecidableEq V]
  {F : Finset (Sym2 V)}
  {e : Sym2 V} :
-- imply
  ons_edgeBit F e = 0 ↔ e ∉ F := by
-- proof
  apply StatMech.Onsager.ons_edgeBit_eq_zero_iff F e

/--
[ons_portEdge_west_eq_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_portEdge_west_eq_horizontal_eq
  {L : ℕ}
  {p : ZMod L × ZMod L} :
-- imply
  ons_portEdge L (p, 2) = ons_portEdge L ((p.1 - 1, p.2), 0) := by
-- proof
  apply StatMech.Onsager.ons_portEdge_west_eq_horizontal L p

/--
[ons_portEdge_south_eq_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_portEdge_south_eq_vertical_eq
  {L : ℕ}
  {p : ZMod L × ZMod L} :
-- imply
  ons_portEdge L (p, 3) = ons_portEdge L ((p.1, p.2 - 1), 1) := by
-- proof
  apply StatMech.Onsager.ons_portEdge_south_eq_vertical L p

/--
[ons_edgeBits_divergence_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_edgeBits_divergence_zero_eq
  {L : ℕ}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
  {p : ZMod L × ZMod L}
-- given
  (hF : F ∈ evenSubgraphs (onsTorusGraph L)) :
-- imply
  ons_horizontalBit F p + ons_horizontalBit F (p.1 - 1, p.2) + ons_verticalBit F p + ons_verticalBit F (p.1, p.2 - 1) = 0 := by
-- proof
  apply StatMech.Onsager.ons_edgeBits_divergence_zero L F hF p

/--
[ons_edgeBit_eq_zero_of_incCount_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_edgeBit_eq_zero_of_incCount_eq_zero_eq
  [Fintype V]
  [DecidableEq V]
  {F : Finset (Sym2 V)}
  {v : V}
  {e : Sym2 V}
-- given
  (hinc : incCount F v = 0)
  (hve : v ∈ e) :
-- imply
  ons_edgeBit F e = 0 := by
-- proof
  apply StatMech.Onsager.ons_edgeBit_eq_zero_of_incCount_eq_zero F v e hinc hve

/--
[ons_horizontalBit_zero_of_incCount_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_horizontalBit_zero_of_incCount_eq_zero_eq
  {L : ℕ}
  [NeZero L]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
  {p : ZMod L × ZMod L}
-- given
  (hinc : incCount F p = 0) :
-- imply
  ons_horizontalBit F p = 0 := by
-- proof
  apply StatMech.Onsager.ons_horizontalBit_zero_of_incCount_eq_zero F p hinc

/--
[ons_verticalBit_zero_of_incCount_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_verticalBit_zero_of_incCount_eq_zero_eq
  {L : ℕ}
  [NeZero L]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
  {p : ZMod L × ZMod L}
-- given
  (hinc : incCount F p = 0) :
-- imply
  ons_verticalBit F p = 0 := by
-- proof
  apply StatMech.Onsager.ons_verticalBit_zero_of_incCount_eq_zero F p hinc

/--
[ons_verticalBit_pred_zero_of_incCount_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_verticalBit_pred_zero_of_incCount_eq_zero_eq
  {L : ℕ}
  [NeZero L]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
  {p : ZMod L × ZMod L}
-- given
  (hinc : incCount F p = 0) :
-- imply
  ons_verticalBit F (p.1, p.2 - 1) = 0 := by
-- proof
  apply StatMech.Onsager.ons_verticalBit_pred_zero_of_incCount_eq_zero F p hinc

/--
[ons_horizontalBit_pred_zero_of_incCount_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_horizontalBit_pred_zero_of_incCount_eq_zero_eq
  {L : ℕ}
  [NeZero L]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
  {p : ZMod L × ZMod L}
-- given
  (hinc : incCount F p = 0) :
-- imply
  ons_horizontalBit F (p.1 - 1, p.2) = 0 := by
-- proof
  apply StatMech.Onsager.ons_horizontalBit_pred_zero_of_incCount_eq_zero F p hinc

/--
[ons_edgeCycleIntersection_eq_zero_of_incCount_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_edgeCycleIntersection_eq_zero_of_incCount_disjoint_eq
  {L : ℕ}
  [NeZero L]
  {F G : Finset (Sym2 (ZMod L × ZMod L))}
-- given
  (hdisj : ∀ p, incCount F p = 0 ∨ incCount G p = 0) :
-- imply
  ons_edgeCycleIntersection F G = 0 := by
-- proof
  apply StatMech.Onsager.ons_edgeCycleIntersection_eq_zero_of_incCount_disjoint F G hdisj

/--
[ons_edgeZBits_divergence_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_edgeZBits_divergence_zero_eq
  {L : ℕ}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
  {p : ZMod L × ZMod L}
-- given
  (hF : F ∈ evenSubgraphs (onsTorusGraph L)) :
-- imply
  ons_horizontalZBit F p + ons_horizontalZBit F (p.1 - 1, p.2) + ons_verticalZBit F p + ons_verticalZBit F (p.1, p.2 - 1) = 0 := by
-- proof
  apply StatMech.Onsager.ons_edgeZBits_divergence_zero L F hF p

/--
[ons_xFlux_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_xFlux_pred_eq
  {L : ℕ}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
  {x : ZMod L}
-- given
  (hF : F ∈ evenSubgraphs (onsTorusGraph L)) :
-- imply
  ons_xFlux F x = ons_xFlux F (x - 1) := by
-- proof
  apply StatMech.Onsager.ons_xFlux_pred L F hF x

/--
[ons_yFlux_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_yFlux_pred_eq
  {L : ℕ}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
  {y : ZMod L}
-- given
  (hF : F ∈ evenSubgraphs (onsTorusGraph L)) :
-- imply
  ons_yFlux F y = ons_yFlux F (y - 1) := by
-- proof
  apply StatMech.Onsager.ons_yFlux_pred L F hF y

/--
[ons_xSeamPortEdge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_xSeamPortEdge_injective_eq
  {L : ℕ}
  [Fact (2 < L)] :
-- imply
  Function.Injective (ons_xSeamPortEdge L) := by
-- proof
  apply StatMech.Onsager.ons_xSeamPortEdge_injective L

/--
[ons_ySeamPortEdge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_ySeamPortEdge_injective_eq
  {L : ℕ}
  [Fact (2 < L)] :
-- imply
  Function.Injective (ons_ySeamPortEdge L) := by
-- proof
  apply StatMech.Onsager.ons_ySeamPortEdge_injective L

/--
[ons_xSeamEdge_xSeamPortEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_xSeamEdge_xSeamPortEdge_eq
  {L : ℕ}
  {y : ZMod L} :
-- imply
  ons_xSeamEdge L (ons_xSeamPortEdge L y) := by
-- proof
  apply StatMech.Onsager.ons_xSeamEdge_xSeamPortEdge L y

/--
[ons_ySeamEdge_ySeamPortEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_ySeamEdge_ySeamPortEdge_eq
  {L : ℕ}
  {x : ZMod L} :
-- imply
  ons_ySeamEdge L (ons_ySeamPortEdge L x) := by
-- proof
  apply StatMech.Onsager.ons_ySeamEdge_ySeamPortEdge L x

/--
[ons_filter_xSeam_eq_image](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_filter_xSeam_eq_image_eq
  {L : ℕ}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))} :
-- imply
  F.filter (ons_xSeamEdge L) = (Finset.univ.filter (fun y : ZMod L => ons_xSeamPortEdge L y ∈ F)).image (ons_xSeamPortEdge L) := by
-- proof
  apply StatMech.Onsager.ons_filter_xSeam_eq_image L F

/--
[ons_filter_ySeam_eq_image](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_filter_ySeam_eq_image_eq
  {L : ℕ}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))} :
-- imply
  F.filter (ons_ySeamEdge L) = (Finset.univ.filter (fun x : ZMod L => ons_ySeamPortEdge L x ∈ F)).image (ons_ySeamPortEdge L) := by
-- proof
  apply StatMech.Onsager.ons_filter_ySeam_eq_image L F

/--
[ons_xFlux_neg_one_eq_seamCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_xFlux_neg_one_eq_seamCard_eq
  {L : ℕ}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))} :
-- imply
  ons_xFlux F (-1) = ((F.filter (ons_xSeamEdge L)).card : ZMod 2) := by
-- proof
  apply StatMech.Onsager.ons_xFlux_neg_one_eq_seamCard L F

/--
[ons_yFlux_neg_one_eq_seamCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_yFlux_neg_one_eq_seamCard_eq
  {L : ℕ}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))} :
-- imply
  ons_yFlux F (-1) = ((F.filter (ons_ySeamEdge L)).card : ZMod 2) := by
-- proof
  apply StatMech.Onsager.ons_yFlux_neg_one_eq_seamCard L F

/--
[ons_evenHomology_fst_cast_eq_xFlux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_evenHomology_fst_cast_eq_xFlux_eq
  {L : ℕ}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))} :
-- imply
  ((ons_evenHomology L F).1 : ZMod 2) = ons_xFlux F (-1) := by
-- proof
  apply StatMech.Onsager.ons_evenHomology_fst_cast_eq_xFlux L F

/--
[ons_evenHomology_snd_cast_eq_yFlux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_evenHomology_snd_cast_eq_yFlux_eq
  {L : ℕ}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))} :
-- imply
  ((ons_evenHomology L F).2 : ZMod 2) = ons_yFlux F (-1) := by
-- proof
  apply StatMech.Onsager.ons_evenHomology_snd_cast_eq_yFlux L F

/--
[ons_sum_range_succ_first](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_sum_range_succ_first_eq
  [AddCommMonoid A]
  {f : ℕ → A}
  {n : ℕ} :
-- imply
  ∑ i ∈ Finset.range (n + 1), f i = f 0 + ∑ i ∈ Finset.range n, f (i + 1) := by
-- proof
  apply StatMech.Onsager.ons_sum_range_succ_first f n

/--
[ons_sum_zmod_eq_sum_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_sum_zmod_eq_sum_range_eq
  [AddCommMonoid A]
  {L : ℕ}
  [NeZero L]
  {f : ZMod L → A} :
-- imply
  ∑ z : ZMod L, f z = ∑ i ∈ Finset.range L, f (i : ZMod L) := by
-- proof
  apply StatMech.Onsager.ons_sum_zmod_eq_sum_range L f

/--
[ons_zmodPrefix_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_zmodPrefix_zero_eq
  [AddCommMonoid A]
  {L : ℕ}
  [NeZero L]
  {f : ZMod L → A} :
-- imply
  ons_zmodPrefix f 0 = 0 := by
-- proof
  apply StatMech.Onsager.ons_zmodPrefix_zero f

/--
[ons_zmodPrefix_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_zmodPrefix_add_one_eq
  [AddCommMonoid A]
  {L : ℕ}
  [Fact (2 < L)]
  {f : ZMod L → A}
  {z : ZMod L}
-- given
  (hz : z ≠ -1) :
-- imply
  ons_zmodPrefix f (z + 1) = ons_zmodPrefix f z + f (z + 1) := by
-- proof
  apply StatMech.Onsager.ons_zmodPrefix_add_one f z hz

/--
[ons_zmodPrefix_eq_add_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_zmodPrefix_eq_add_pred_eq
  [AddCommMonoid A]
  {L : ℕ}
  [Fact (2 < L)]
  {f : ZMod L → A}
  {z : ZMod L}
-- given
  (hz : z ≠ 0) :
-- imply
  ons_zmodPrefix f z = ons_zmodPrefix f (z - 1) + f z := by
-- proof
  apply StatMech.Onsager.ons_zmodPrefix_eq_add_pred f z hz

/--
[ons_zmodPrefix_neg_one_of_sum_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_zmodPrefix_neg_one_of_sum_zero_eq
  {L : ℕ}
  [Fact (2 < L)]
  {f : ZMod L → ZMod 2}
-- given
  (hsum : ∑ z, f z = 0) :
-- imply
  ons_zmodPrefix f (-1) = f 0 := by
-- proof
  apply StatMech.Onsager.ons_zmodPrefix_neg_one_of_sum_zero f hsum

/--
[ons_zmod_eq_neg_one_of_eq_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_zmod_eq_neg_one_of_eq_pred_eq
  {L : ℕ}
  [Fact (2 < L)]
  {f : ZMod L → A}
  {z : ZMod L}
-- given
  (hpred : ∀ z, f z = f (z - 1)) :
-- imply
  f z = f (-1) := by
-- proof
  apply StatMech.Onsager.ons_zmod_eq_neg_one_of_eq_pred f hpred z

/--
[ons_xFlux_eq_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_xFlux_eq_neg_one_eq
  {L : ℕ}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
  {x : ZMod L}
-- given
  (hF : F ∈ evenSubgraphs (onsTorusGraph L)) :
-- imply
  ons_xFlux F x = ons_xFlux F (-1) := by
-- proof
  apply StatMech.Onsager.ons_xFlux_eq_neg_one L F hF x

/--
[ons_yFlux_eq_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_yFlux_eq_neg_one_eq
  {L : ℕ}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
  {y : ZMod L}
-- given
  (hF : F ∈ evenSubgraphs (onsTorusGraph L)) :
-- imply
  ons_yFlux F y = ons_yFlux F (-1) := by
-- proof
  apply StatMech.Onsager.ons_yFlux_eq_neg_one L F hF y

/--
[ons_zmodPrefix_add_pred_of_sum_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_zmodPrefix_add_pred_of_sum_zero_eq
  {L : ℕ}
  [Fact (2 < L)]
  {f : ZMod L → ZMod 2}
  {z : ZMod L}
-- given
  (hsum : ∑ z, f z = 0) :
-- imply
  ons_zmodPrefix f z + ons_zmodPrefix f (z - 1) = f z := by
-- proof
  apply StatMech.Onsager.ons_zmodPrefix_add_pred_of_sum_zero f hsum z

/--
[ons_zeroFlux_divergence_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_zeroFlux_divergence_zero_eq
  {L : ℕ}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
  {p : ZMod L × ZMod L}
-- given
  (hF : F ∈ evenSubgraphs (onsTorusGraph L)) :
-- imply
  ons_zeroFluxHorizontal F p + ons_zeroFluxHorizontal F (p.1 - 1, p.2) + ons_zeroFluxVertical F p + ons_zeroFluxVertical F (p.1, p.2 - 1) = 0 := by
-- proof
  apply StatMech.Onsager.ons_zeroFlux_divergence_zero L F hF p

/--
[ons_zeroFluxHorizontal_sum_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_zeroFluxHorizontal_sum_zero_eq
  {L : ℕ}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
  {x : ZMod L}
-- given
  (hF : F ∈ evenSubgraphs (onsTorusGraph L)) :
-- imply
  ∑ y : ZMod L, ons_zeroFluxHorizontal F (x, y) = 0 := by
-- proof
  apply StatMech.Onsager.ons_zeroFluxHorizontal_sum_zero L F hF x

/--
[ons_zeroFluxVertical_sum_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_zeroFluxVertical_sum_zero_eq
  {L : ℕ}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
  {y : ZMod L}
-- given
  (hF : F ∈ evenSubgraphs (onsTorusGraph L)) :
-- imply
  ∑ x : ZMod L, ons_zeroFluxVertical F (x, y) = 0 := by
-- proof
  apply StatMech.Onsager.ons_zeroFluxVertical_sum_zero L F hF y

/--
[ons_zeroFluxPotential_vertical_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_zeroFluxPotential_vertical_boundary_eq
  {L : ℕ}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
  {p : ZMod L × ZMod L}
-- given
  (hF : F ∈ evenSubgraphs (onsTorusGraph L)) :
-- imply
  ons_zeroFluxPotential F p + ons_zeroFluxPotential F (p.1 - 1, p.2) = ons_zeroFluxVertical F p := by
-- proof
  apply StatMech.Onsager.ons_zeroFluxPotential_vertical_boundary L F hF p

/--
[ons_zeroFluxPotential_horizontal_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_zeroFluxPotential_horizontal_boundary_eq
  {L : ℕ}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
  {p : ZMod L × ZMod L}
-- given
  (hF : F ∈ evenSubgraphs (onsTorusGraph L)) :
-- imply
  ons_zeroFluxPotential F p + ons_zeroFluxPotential F (p.1, p.2 - 1) = ons_zeroFluxHorizontal F p := by
-- proof
  apply StatMech.Onsager.ons_zeroFluxPotential_horizontal_boundary L F hF p

/--
[ons_zeroFlux_intersection_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_zeroFlux_intersection_eq_zero_eq
  {L : ℕ}
  [Fact (2 < L)]
  {F G : Finset (Sym2 (ZMod L × ZMod L))}
-- given
  (hF : F ∈ evenSubgraphs (onsTorusGraph L))
  (hG : G ∈ evenSubgraphs (onsTorusGraph L)) :
-- imply
  (∑ p : ZMod L × ZMod L, (ons_zeroFluxHorizontal F p * ons_verticalZBit G (p.1, p.2 - 1) + ons_zeroFluxVertical F p * ons_horizontalZBit G (p.1 - 1, p.2))) = 0 := by
-- proof
  apply StatMech.Onsager.ons_zeroFlux_intersection_eq_zero L F G hF hG

/--
[ons_horizontalZBit_eq_zeroFlux_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_horizontalZBit_eq_zeroFlux_add_eq
  {L : ℕ}
  [NeZero L]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
  {p : ZMod L × ZMod L} :
-- imply
  ons_horizontalZBit F p = ons_zeroFluxHorizontal F p + if p.2 = 0 then ons_xFlux F (-1) else 0 := by
-- proof
  apply StatMech.Onsager.ons_horizontalZBit_eq_zeroFlux_add F p

/--
[ons_verticalZBit_eq_zeroFlux_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_verticalZBit_eq_zeroFlux_add_eq
  {L : ℕ}
  [NeZero L]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
  {p : ZMod L × ZMod L} :
-- imply
  ons_verticalZBit F p = ons_zeroFluxVertical F p + if p.1 = 0 then ons_yFlux F (-1) else 0 := by
-- proof
  apply StatMech.Onsager.ons_verticalZBit_eq_zeroFlux_add F p

/--
[ons_horizontalSeam_intersection_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_horizontalSeam_intersection_sum_eq
  {L : ℕ}
  [Fact (2 < L)]
  {F G : Finset (Sym2 (ZMod L × ZMod L))} :
-- imply
  (∑ p : ZMod L × ZMod L, (if p.2 = 0 then ons_xFlux F (-1) else 0) * ons_verticalZBit G (p.1, p.2 - 1)) = ons_xFlux F (-1) * ons_yFlux G (-1) := by
-- proof
  apply StatMech.Onsager.ons_horizontalSeam_intersection_sum L F G

/--
[ons_verticalSeam_intersection_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_verticalSeam_intersection_sum_eq
  {L : ℕ}
  [Fact (2 < L)]
  {F G : Finset (Sym2 (ZMod L × ZMod L))} :
-- imply
  (∑ p : ZMod L × ZMod L, (if p.1 = 0 then ons_yFlux F (-1) else 0) * ons_horizontalZBit G (p.1 - 1, p.2)) = ons_yFlux F (-1) * ons_xFlux G (-1) := by
-- proof
  apply StatMech.Onsager.ons_verticalSeam_intersection_sum L F G

/--
[ons_edgeCycleZIntersection_eq_flux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_edgeCycleZIntersection_eq_flux_eq
  {L : ℕ}
  [Fact (2 < L)]
  {F G : Finset (Sym2 (ZMod L × ZMod L))}
-- given
  (hF : F ∈ evenSubgraphs (onsTorusGraph L))
  (hG : G ∈ evenSubgraphs (onsTorusGraph L)) :
-- imply
  ons_edgeCycleZIntersection F G = ons_xFlux F (-1) * ons_yFlux G (-1) + ons_yFlux F (-1) * ons_xFlux G (-1) := by
-- proof
  apply StatMech.Onsager.ons_edgeCycleZIntersection_eq_flux L F G hF hG

/--
[ons_edgeCycleIntersection_cast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_edgeCycleIntersection_cast_eq
  {L : ℕ}
  [NeZero L]
  {F G : Finset (Sym2 (ZMod L × ZMod L))} :
-- imply
  (ons_edgeCycleIntersection F G : ZMod 2) = ons_edgeCycleZIntersection F G := by
-- proof
  apply StatMech.Onsager.ons_edgeCycleIntersection_cast F G

/--
[ons_homologyIntersection_cast_eq_flux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_homologyIntersection_cast_eq_flux_eq
  {L : ℕ}
  [Fact (2 < L)]
  {F G : Finset (Sym2 (ZMod L × ZMod L))} :
-- imply
  (ons_homologyIntersection (ons_evenHomology L F) (ons_evenHomology L G) : ZMod 2) = ons_xFlux F (-1) * ons_yFlux G (-1) + ons_yFlux F (-1) * ons_xFlux G (-1) := by
-- proof
  apply StatMech.Onsager.ons_homologyIntersection_cast_eq_flux L F G

/--
[ons_edgeCycleIntersection_eq_homologyIntersection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_edgeCycleIntersection_eq_homologyIntersection_eq
  {L : ℕ}
  [Fact (2 < L)]
  {F G : Finset (Sym2 (ZMod L × ZMod L))}
-- given
  (hF : F ∈ evenSubgraphs (onsTorusGraph L))
  (hG : G ∈ evenSubgraphs (onsTorusGraph L)) :
-- imply
  ons_edgeCycleIntersection F G = ons_homologyIntersection (ons_evenHomology L F) (ons_evenHomology L G) := by
-- proof
  apply StatMech.Onsager.ons_edgeCycleIntersection_eq_homologyIntersection L F G hF hG

/--
[ons_walk_edges_incCount_eq_zero_of_not_mem_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_walk_edges_incCount_eq_zero_of_not_mem_support_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {u v : V}
  {p : G.Walk u v}
  {z : V}
-- given
  (hz : z ∉ p.support) :
-- imply
  incCount p.edges.toFinset z = 0 := by
-- proof
  apply StatMech.Onsager.ons_walk_edges_incCount_eq_zero_of_not_mem_support p z hz

/--
[ons_walk_edges_incCounts_disjoint_of_support_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_walk_edges_incCounts_disjoint_of_support_disjoint_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {u v x y : V}
  {p : G.Walk u v}
  {q : G.Walk x y}
-- given
  (hdisj : List.Disjoint p.support q.support) :
-- imply
  ∀ z, incCount p.edges.toFinset z = 0 ∨ incCount q.edges.toFinset z = 0 := by
-- proof
  apply StatMech.Onsager.ons_walk_edges_incCounts_disjoint_of_support_disjoint p q hdisj

/--
[ons_homologyIntersection_eq_zero_of_incCount_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_homologyIntersection_eq_zero_of_incCount_disjoint_eq
  {L : ℕ}
  [Fact (2 < L)]
  {F G : Finset (Sym2 (ZMod L × ZMod L))}
-- given
  (hF : F ∈ evenSubgraphs (onsTorusGraph L))
  (hG : G ∈ evenSubgraphs (onsTorusGraph L))
  (hdisj : ∀ p, incCount F p = 0 ∨ incCount G p = 0) :
-- imply
  ons_homologyIntersection (ons_evenHomology L F) (ons_evenHomology L G) = 0 := by
-- proof
  apply StatMech.Onsager.ons_homologyIntersection_eq_zero_of_incCount_disjoint L F G hF hG hdisj

/--
[ons_decEmbedWalk_originalHomology_isotropic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_decEmbedWalk_originalHomology_isotropic_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d e : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
  {p : (ons_decGraph L).Walk e e}
-- given
  (hq : q.IsCycle)
  (hp : p.IsCycle)
  (hqsnd : q.snd = ons_dartRev L d)
  (hpsnd : p.snd = ons_dartRev L e)
  (hdisj : Disjoint q.toSubgraph.verts p.toSubgraph.verts) :
-- imply
  ons_homologyIntersection (ons_evenHomology L (ons_walkOriginalEdges q)) (ons_evenHomology L (ons_walkOriginalEdges p)) = 0 := by
-- proof
  apply StatMech.Onsager.ons_decEmbedWalk_originalHomology_isotropic L q p hq hp hqsnd hpsnd hdisj

/--
[ons_decCycles_originalHomology_isotropic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_decCycles_originalHomology_isotropic_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d e : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
  {p : (ons_decGraph L).Walk e e}
-- given
  (hq : q.IsCycle)
  (hp : p.IsCycle)
  (hdisj : Disjoint q.toSubgraph.verts p.toSubgraph.verts) :
-- imply
  ons_homologyIntersection (ons_evenHomology L (ons_walkOriginalEdges q)) (ons_evenHomology L (ons_walkOriginalEdges p)) = 0 := by
-- proof
  apply StatMech.Onsager.ons_decCycles_originalHomology_isotropic L q p hq hp hdisj

/--
[ons_decCycleFamily_originalHomology_isotropic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean)
-/
@[path]
private lemma ons_decCycleFamily_originalHomology_isotropic_eq
  {L : ℕ}
  [Fact (2 < L)]
  [Fintype ι]
  [DecidableEq ι]
  {base : ι → ons_Dart L}
  {p : (i : ι) → (ons_decGraph L).Walk (base i) (base i)}
-- given
  (hcycle : ∀ i, (p i).IsCycle)
  (hverts : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint (fun i ↦ (p i).toSubgraph.verts)) :
-- imply
  ∀ i j, i ≠ j → ons_homologyIntersection (ons_evenHomology L (ons_walkOriginalEdges (p i))) (ons_evenHomology L (ons_walkOriginalEdges (p j))) = 0 := by
-- proof
  apply StatMech.Onsager.ons_decCycleFamily_originalHomology_isotropic L base p hcycle hverts


-- created on 2026-10-23

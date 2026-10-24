import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.DecorationInternalMiddle
open StatMech StatMech.Onsager


/--
[ons_fin3_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationInternalMiddle.lean)
-/
@[path]
private lemma ons_fin3_univ_eq :
-- imply
  (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by
-- proof
  apply StatMech.Onsager.ons_fin3_univ

/--
[ons_decChainPathIndices_one_mem_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationInternalMiddle.lean)
-/
@[path]
private lemma ons_decChainPathIndices_one_mem_iff_eq
  {a b : Fin 4} :
-- imply
  (1 : Fin 3) ∈ ons_decChainPathIndices a b ↔ ons_decMiddleSide a ≠ ons_decMiddleSide b := by
-- proof
  apply StatMech.Onsager.ons_decChainPathIndices_one_mem_iff a b

/--
[ons_decTransitionWeight_scale_chain_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationInternalMiddle.lean)
-/
@[path]
private lemma ons_decTransitionWeight_scale_chain_one_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {site : ZMod L × ZMod L}
  {t : ℂ}
  {d₂ d₁ : ons_Dart L} :
-- imply
  ons_decTransitionWeight L (ons_scaleDecEdgeWeight decWeight (ons_decChainEdge site 1) t) d₂ d₁ = if d₂.1 = site ∧ (1 : Fin 3) ∈ ons_decChainPathIndices (d₁.2 + 2) d₂.2 then t * ons_decTransitionWeight L decWeight d₂ d₁ else ons_decTransitionWeight L decWeight d₂ d₁ := by
-- proof
  apply StatMech.Onsager.ons_decTransitionWeight_scale_chain_one L decWeight site t d₂ d₁

/--
[ons_decMiddle_mul_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationInternalMiddle.lean)
-/
@[path]
private lemma ons_decMiddle_mul_apply_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {omega u v : ℂ}
  {site : ZMod L × ZMod L}
  {d₂ d₁ : ons_Dart L}
-- given
  (homega : omega ≠ 0) :
-- imply
  (ons_decMiddleU L decWeight omega site * ons_decMiddleV L decWeight omega u v site) d₂ d₁ = if d₂.1 = site ∧ (1 : Fin 3) ∈ ons_decChainPathIndices (d₁.2 + 2) d₂.2 then ons_KWmatDecorationWeightedPhase L decWeight omega u v d₂ d₁ else 0 := by
-- proof
  apply StatMech.Onsager.ons_decMiddle_mul_apply L decWeight omega u v homega site d₂ d₁

/--
[ons_KWmatDecorationWeightedPhase_scaleMiddle_rankTwo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationInternalMiddle.lean)
-/
@[path]
private lemma ons_KWmatDecorationWeightedPhase_scaleMiddle_rankTwo_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {omega u v t : ℂ}
  {site : ZMod L × ZMod L}
-- given
  (homega : omega ≠ 0) :
-- imply
  ons_KWmatDecorationWeightedPhase L (ons_scaleDecEdgeWeight decWeight (ons_decChainEdge site 1) t) omega u v = ons_KWmatDecorationWeightedPhase L (ons_scaleDecEdgeWeight decWeight (ons_decChainEdge site 1) 0) omega u v + t • (ons_decMiddleU L decWeight omega site * ons_decMiddleV L decWeight omega u v site) := by
-- proof
  apply StatMech.Onsager.ons_KWmatDecorationWeightedPhase_scaleMiddle_rankTwo L decWeight omega u v t homega site

/--
[ons_decMiddleAugmented_det](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationInternalMiddle.lean)
-/
@[path]
private lemma ons_decMiddleAugmented_det_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {omega u v t : ℂ}
  {site : ZMod L × ZMod L}
-- given
  (homega : omega ≠ 0) :
-- imply
  (1 - ons_decMiddleAugmented L decWeight omega u v t site).det = (1 - ons_KWmatDecorationWeightedPhase L (ons_scaleDecEdgeWeight decWeight (ons_decChainEdge site 1) t) omega u v).det := by
-- proof
  apply StatMech.Onsager.ons_decMiddleAugmented_det L decWeight omega u v t homega site


-- created on 2026-10-23

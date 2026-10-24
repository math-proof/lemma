import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.KWEdgeScale
open StatMech StatMech.Onsager


/--
[ons_KWmatWeightedPhase_scaleEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWEdgeScale.lean)
-/
@[path]
private lemma ons_KWmatWeightedPhase_scaleEdge_eq
  {L : ℕ}
  [Fact (2 < L)]
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {omega u v t : ℂ}
  {e : ons_Dart L} :
-- imply
  ons_KWmatWeightedPhase L (ons_scaleEdgeWeight weight (ons_portEdge L e) t) omega u v = ons_scaleColumns ({e, ons_dartRev L e} : Finset (ons_Dart L)) t (ons_KWmatWeightedPhase L weight omega u v) := by
-- proof
  apply StatMech.Onsager.ons_KWmatWeightedPhase_scaleEdge L weight omega u v t e

/--
[ons_mask_scaleColumns](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWEdgeScale.lean)
-/
@[path]
private lemma ons_mask_scaleColumns_eq
  [DecidableEq E]
  {forbidden S : Finset E}
  {t : ℂ}
  {Lambda : Matrix E E ℂ} :
-- imply
  ons_maskMatrix forbidden (ons_scaleColumns S t Lambda) = ons_scaleColumns S t (ons_maskMatrix forbidden Lambda) := by
-- proof
  apply StatMech.Onsager.ons_mask_scaleColumns forbidden S t Lambda

/--
[ons_mask_KWmatWeightedPhase_scaleEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWEdgeScale.lean)
-/
@[path]
private lemma ons_mask_KWmatWeightedPhase_scaleEdge_eq
  {L : ℕ}
  [Fact (2 < L)]
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {omega u v t : ℂ}
  {forbidden : Finset (ons_Dart L)}
  {e : ons_Dart L} :
-- imply
  ons_maskMatrix forbidden (ons_KWmatWeightedPhase L (ons_scaleEdgeWeight weight (ons_portEdge L e) t) omega u v) = ons_scaleColumns ({e, ons_dartRev L e} : Finset (ons_Dart L)) t (ons_maskMatrix forbidden (ons_KWmatWeightedPhase L weight omega u v)) := by
-- proof
  apply StatMech.Onsager.ons_mask_KWmatWeightedPhase_scaleEdge L weight omega u v t forbidden e

/--
[ons_tsum_firstReturnWeight_scaleEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWEdgeScale.lean)
-/
@[path]
private lemma ons_tsum_firstReturnWeight_scaleEdge_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {omega u v t : ℂ}
  {forbidden : Finset (ons_Dart L)}
  {e : ons_Dart L} :
-- imply
  (∑' s, ons_firstReturnWeight (ons_maskMatrix forbidden (ons_KWmatWeightedPhase L (ons_scaleEdgeWeight weight (ons_portEdge L e) t) omega u v)) e (ons_dartRev L e) s) = t * ∑' s, ons_firstReturnWeight (ons_maskMatrix forbidden (ons_KWmatWeightedPhase L weight omega u v)) e (ons_dartRev L e) s := by
-- proof
  apply StatMech.Onsager.ons_tsum_firstReturnWeight_scaleEdge L weight omega u v t forbidden e


-- created on 2026-10-23

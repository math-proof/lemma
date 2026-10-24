import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.KWZeroEdge
open StatMech StatMech.Onsager


/--
[ons_loopWeight_scaleColumns_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWZeroEdge.lean)
-/
@[path]
private lemma ons_loopWeight_scaleColumns_zero_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {S : Finset E}
  {Lambda : Matrix E E ℂ}
  {d : Fin n → E} :
-- imply
  ons_loopWeight (ons_scaleColumns S 0 Lambda) d = if ∃ k, d k ∈ S then 0 else ons_loopWeight Lambda d := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_scaleColumns_zero S Lambda d

/--
[ons_detWalkRoot_scaleColumns_zero_eq_mask](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWZeroEdge.lean)
-/
@[path]
private lemma ons_detWalkRoot_scaleColumns_zero_eq_mask_eq
  [Fintype E]
  [DecidableEq E]
  {S : Finset E}
  {Lambda : Matrix E E ℂ} :
-- imply
  ons_detWalkRoot (ons_scaleColumns S 0 Lambda) = ons_detWalkRoot (ons_maskMatrix S Lambda) := by
-- proof
  apply StatMech.Onsager.ons_detWalkRoot_scaleColumns_zero_eq_mask S Lambda

/--
[ons_detWalkRoot_zeroEdge_eq_mask](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWZeroEdge.lean)
-/
@[path]
private lemma ons_detWalkRoot_zeroEdge_eq_mask_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {omega u v : ℂ}
  {e : ons_Dart L} :
-- imply
  ons_detWalkRoot (ons_KWmatWeightedPhase L (ons_scaleEdgeWeight weight (ons_portEdge L e) 0) omega u v) = ons_detWalkRoot (ons_maskMatrix ({e, ons_dartRev L e} : Finset (ons_Dart L)) (ons_KWmatWeightedPhase L weight omega u v)) := by
-- proof
  apply StatMech.Onsager.ons_detWalkRoot_zeroEdge_eq_mask L weight omega u v e


-- created on 2026-10-23

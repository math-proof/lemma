import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.SpinWeightedRecurrence
open StatMech StatMech.Onsager


/--
[ons_weightedRoot_eq_spin_scaleEdge_of_coefficient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinWeightedRecurrence.lean)
-/
@[path]
private lemma ons_weightedRoot_eq_spin_scaleEdge_of_coefficient_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {a b : Fin 2}
  {q : ℝ}
  {t : ℂ}
  {e : ons_Dart L}
-- given
  (hq : 0 ≤ q)
  (hweight : ∀ edge, ‖weight edge‖ ≤ q)
  (ht : ‖t‖ ≤ 1)
  (hsmall : q < (2 * (Fintype.card (ons_Dart L) : ℝ) ^ 2)⁻¹)
  (hzero : ons_detWalkRoot (ons_KWmatWeightedPhase L (ons_scaleEdgeWeight weight (ons_portEdge L e) 0) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) = ons_weightedSpinCharacterSum L (ons_scaleEdgeWeight weight (ons_portEdge L e) 0) a b)
  (hcoeff : ons_weightedSpinEdgeCoefficient L weight a b (ons_portEdge L e) = -ons_detWalkRoot (ons_maskMatrix ({e, ons_dartRev L e} : Finset (ons_Dart L)) (ons_KWmatWeightedPhase L weight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b))) * (∑' s, ons_firstReturnWeight (ons_KWmatWeightedPhase L weight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) e (ons_dartRev L e) s)) :
-- imply
  ons_detWalkRoot (ons_KWmatWeightedPhase L (ons_scaleEdgeWeight weight (ons_portEdge L e) t) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) = ons_weightedSpinCharacterSum L (ons_scaleEdgeWeight weight (ons_portEdge L e) t) a b := by
-- proof
  apply StatMech.Onsager.ons_weightedRoot_eq_spin_scaleEdge_of_coefficient L weight a b q hq hweight t ht e hsmall hzero hcoeff


-- created on 2026-10-23

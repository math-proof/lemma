import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.KWMultiaffineBounded
open StatMech StatMech.Onsager


/--
[norm_ons_scaleEdgeWeight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWMultiaffineBounded.lean)
-/
@[path]
private lemma norm_ons_scaleEdgeWeight_le_eq
  {L : ℕ}
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {edge : Sym2 (ZMod L × ZMod L)}
  {t : ℂ}
  {q : ℝ}
  {f : Sym2 (ZMod L × ZMod L)}
-- given
  (hq : 0 ≤ q)
  (hweight : ∀ f, ‖weight f‖ ≤ q)
  (ht : ‖t‖ ≤ 1) :
-- imply
  ‖ons_scaleEdgeWeight weight edge t f‖ ≤ q := by
-- proof
  apply StatMech.Onsager.norm_ons_scaleEdgeWeight_le weight edge t q hq hweight ht f

/--
[ons_detWalkRoot_scaleEdge_affine_of_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWMultiaffineBounded.lean)
-/
@[path]
private lemma ons_detWalkRoot_scaleEdge_affine_of_bound_eq
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
  (hsmall : q < (2 * (Fintype.card (ons_Dart L) : ℝ) ^ 2)⁻¹) :
-- imply
  ons_detWalkRoot (ons_KWmatWeightedPhase L (ons_scaleEdgeWeight weight (ons_portEdge L e) t) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) = ons_detWalkRoot (ons_maskMatrix ({e, ons_dartRev L e} : Finset (ons_Dart L)) (ons_KWmatWeightedPhase L weight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b))) * (1 - t * ∑' s, ons_firstReturnWeight (ons_KWmatWeightedPhase L weight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) e (ons_dartRev L e) s) := by
-- proof
  apply StatMech.Onsager.ons_detWalkRoot_scaleEdge_affine_of_bound L weight a b q hq hweight t ht e hsmall


-- created on 2026-10-23

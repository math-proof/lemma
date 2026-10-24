import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.KWMultiaffine
open StatMech StatMech.Onsager


/--
[ons_mask_scaleColumns_absorb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWMultiaffine.lean)
-/
@[path]
private lemma ons_mask_scaleColumns_absorb_eq
  [DecidableEq E]
  {forbidden S : Finset E}
  {t : ℂ}
  {Lambda : Matrix E E ℂ}
-- given
  (hsub : S ⊆ forbidden) :
-- imply
  ons_maskMatrix forbidden (ons_scaleColumns S t Lambda) = ons_maskMatrix forbidden Lambda := by
-- proof
  apply StatMech.Onsager.ons_mask_scaleColumns_absorb forbidden S t Lambda hsub

/--
[ons_detWalkRoot_scaleEdge_affine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWMultiaffine.lean)
-/
@[path]
private lemma ons_detWalkRoot_scaleEdge_affine_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {omega : ℂ}
  {a b : Fin 2}
  {q : ℝ}
  {t : ℂ}
  {e : ons_Dart L}
-- given
  (homega : omega ^ 2 = Complex.I)
  (hq : 0 ≤ q)
  (hentryScaled : ∀ d2 d1, ‖ons_KWmatWeightedPhase L (ons_scaleEdgeWeight weight (ons_portEdge L e) t) omega (ons_spinPhase L a) (ons_spinPhase L b) d2 d1‖ ≤ q)
  (hsmall : q < (2 * (Fintype.card (ons_Dart L) : ℝ) ^ 2)⁻¹)
  (hcard : (Fintype.card (ons_Dart L) : ℝ) * q < 1) :
-- imply
  ons_detWalkRoot (ons_KWmatWeightedPhase L (ons_scaleEdgeWeight weight (ons_portEdge L e) t) omega (ons_spinPhase L a) (ons_spinPhase L b)) = ons_detWalkRoot (ons_maskMatrix ({e, ons_dartRev L e} : Finset (ons_Dart L)) (ons_KWmatWeightedPhase L weight omega (ons_spinPhase L a) (ons_spinPhase L b))) * (1 - t * ∑' s, ons_firstReturnWeight (ons_KWmatWeightedPhase L weight omega (ons_spinPhase L a) (ons_spinPhase L b)) e (ons_dartRev L e) s) := by
-- proof
  apply StatMech.Onsager.ons_detWalkRoot_scaleEdge_affine L weight omega homega a b q hq t e hentryScaled hsmall hcard


-- created on 2026-10-23

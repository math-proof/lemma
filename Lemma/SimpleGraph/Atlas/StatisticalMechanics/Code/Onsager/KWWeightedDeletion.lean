import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.KWWeightedDeletion
open StatMech StatMech.Onsager


/--
[ons_detWalkRoot_weighted_mask_delete_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWWeightedDeletion.lean)
-/
@[path]
private lemma ons_detWalkRoot_weighted_mask_delete_pair_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {omega : ℂ}
  {a b : Fin 2}
  {q : ℝ}
  {forbidden : Finset (ons_Dart L)}
  {e : ons_Dart L}
-- given
  (homega : omega ^ 2 = Complex.I)
  (hq : 0 ≤ q)
  (hentryM : ∀ d2 d1, ‖ons_KWmatWeightedPhase L weight omega (ons_spinPhase L a) (ons_spinPhase L b) d2 d1‖ ≤ q)
  (hsmall : q < (2 * (Fintype.card (ons_Dart L) : ℝ) ^ 2)⁻¹)
  (hcard : (Fintype.card (ons_Dart L) : ℝ) * q < 1)
  (hforbidden : ∀ d, ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden) :
-- imply
  ons_detWalkRoot (ons_maskMatrix forbidden (ons_KWmatWeightedPhase L weight omega (ons_spinPhase L a) (ons_spinPhase L b))) = ons_detWalkRoot (ons_maskMatrix (({e, ons_dartRev L e} : Finset (ons_Dart L)) ∪ forbidden) (ons_KWmatWeightedPhase L weight omega (ons_spinPhase L a) (ons_spinPhase L b))) * (1 - ∑' s, ons_firstReturnWeight (ons_maskMatrix forbidden (ons_KWmatWeightedPhase L weight omega (ons_spinPhase L a) (ons_spinPhase L b))) e (ons_dartRev L e) s) := by
-- proof
  apply StatMech.Onsager.ons_detWalkRoot_weighted_mask_delete_pair L weight omega homega a b q hq hentryM hsmall hcard forbidden hforbidden e


-- created on 2026-10-23

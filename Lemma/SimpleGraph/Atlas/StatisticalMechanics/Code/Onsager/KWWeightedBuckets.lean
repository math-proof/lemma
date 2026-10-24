import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.KWWeightedBuckets
open StatMech StatMech.Onsager


/--
[ons_KWmatWeightedPhase_loopSum_two_bucket](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWWeightedBuckets.lean)
-/
@[path]
private lemma ons_KWmatWeightedPhase_loopSum_two_bucket_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {n : ℕ}
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {omega : ℂ}
  {a b : Fin 2}
  {e : ons_Dart L}
-- given
  (homega : omega ^ 2 = Complex.I) :
-- imply
  (∑ d : Fin (n + 1) → ons_Dart L, ons_loopWeight (ons_KWmatWeightedPhase L weight omega (ons_spinPhase L a) (ons_spinPhase L b)) d) = 2 * ons_weightedPhaseBucketE L weight omega a b e n + ons_weightedPhaseBucketN L weight omega a b e n := by
-- proof
  apply StatMech.Onsager.ons_KWmatWeightedPhase_loopSum_two_bucket weight omega homega a b e

/--
[ons_KWmatWeightedPhase_mask_loopSum_two_bucket](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWWeightedBuckets.lean)
-/
@[path]
private lemma ons_KWmatWeightedPhase_mask_loopSum_two_bucket_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {n : ℕ}
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {omega : ℂ}
  {a b : Fin 2}
  {forbidden : Finset (ons_Dart L)}
  {e : ons_Dart L}
-- given
  (homega : omega ^ 2 = Complex.I)
  (hforbidden : ∀ d, ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden) :
-- imply
  (∑ d : Fin (n + 1) → ons_Dart L, ons_loopWeight (ons_maskMatrix forbidden (ons_KWmatWeightedPhase L weight omega (ons_spinPhase L a) (ons_spinPhase L b))) d) = 2 * ons_maskWeightedPhaseBucketE L weight omega a b forbidden e n + ons_maskWeightedPhaseBucketN L weight omega a b forbidden e n := by
-- proof
  apply StatMech.Onsager.ons_KWmatWeightedPhase_mask_loopSum_two_bucket weight omega homega a b forbidden hforbidden e


-- created on 2026-10-23

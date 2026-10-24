import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.ShermanBucketCancellation
open StatMech StatMech.Onsager


/--
[ons_rootedListSeries_eq_lengthSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanBucketCancellation.lean)
-/
@[path]
private lemma ons_rootedListSeries_eq_lengthSum_eq
  [Fintype E]
  [DecidableEq E]
  {Lambda : Matrix E E ℂ}
  {e r : E}
-- given
  (her : e ≠ r)
  (hsum : Summable fun s => ‖ons_firstReturnWeight Lambda e r s‖)
  (hsmall : ∑' s, ‖ons_firstReturnWeight Lambda e r s‖ < 1) :
-- imply
  (∑' w : {w : List E // ons_validRootedList e r w}, ons_rootedListTerm Lambda e w.1) = ∑' n : ℕ, ∑ v ∈ Finset.univ.filter (fun v : Fin (n + 1) → E => v 0 = e ∧ ∀ j, v j ≠ r), ons_loopWeight Lambda v / (ons_visitCount e v : ℂ) := by
-- proof
  apply StatMech.Onsager.ons_rootedListSeries_eq_lengthSum Lambda e r her hsum hsmall

/--
[ons_summable_rootedLengthSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanBucketCancellation.lean)
-/
@[path]
private lemma ons_summable_rootedLengthSum_eq
  [Fintype E]
  [DecidableEq E]
  {Lambda : Matrix E E ℂ}
  {e r : E}
-- given
  (her : e ≠ r)
  (hsum : Summable fun s => ‖ons_firstReturnWeight Lambda e r s‖)
  (hsmall : ∑' s, ‖ons_firstReturnWeight Lambda e r s‖ < 1) :
-- imply
  Summable fun n : ℕ => ∑ v ∈ Finset.univ.filter (fun v : Fin (n + 1) → E => v 0 = e ∧ ∀ j, v j ≠ r), ons_loopWeight Lambda v / (ons_visitCount e v : ℂ) := by
-- proof
  apply StatMech.Onsager.ons_summable_rootedLengthSum Lambda e r her hsum hsmall

/--
[ons_loopBucketSeries_eq_geometric](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanBucketCancellation.lean)
-/
@[path]
private lemma ons_loopBucketSeries_eq_geometric_eq
  [Fintype E]
  [DecidableEq E]
  {Lambda : Matrix E E ℂ}
  {e r : E}
-- given
  (her : e ≠ r)
  (hsum : Summable fun s => ‖ons_firstReturnWeight Lambda e r s‖)
  (hsmall : ∑' s, ‖ons_firstReturnWeight Lambda e r s‖ < 1) :
-- imply
  (∑' n : ℕ, (∑ v ∈ Finset.univ.filter (fun v : Fin (n + 1) → E => (∃ k, v k = e) ∧ ∀ j, v j ≠ r), ons_loopWeight Lambda v) / ((n : ℂ) + 1)) = ∑' k : ℕ, (∑' s, ons_firstReturnWeight Lambda e r s) ^ (k + 1) / (k + 1) := by
-- proof
  apply StatMech.Onsager.ons_loopBucketSeries_eq_geometric Lambda e r her hsum hsmall

/--
[ons_summable_loopBucketSeries](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanBucketCancellation.lean)
-/
@[path]
private lemma ons_summable_loopBucketSeries_eq
  [Fintype E]
  [DecidableEq E]
  {Lambda : Matrix E E ℂ}
  {e r : E}
-- given
  (her : e ≠ r)
  (hsum : Summable fun s => ‖ons_firstReturnWeight Lambda e r s‖)
  (hsmall : ∑' s, ‖ons_firstReturnWeight Lambda e r s‖ < 1) :
-- imply
  Summable fun n : ℕ => (∑ v ∈ Finset.univ.filter (fun v : Fin (n + 1) → E => (∃ k, v k = e) ∧ ∀ j, v j ≠ r), ons_loopWeight Lambda v) / ((n : ℂ) + 1) := by
-- proof
  apply StatMech.Onsager.ons_summable_loopBucketSeries Lambda e r her hsum hsmall

/--
[ons_bucketESeries_eq_geometric](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanBucketCancellation.lean)
-/
@[path]
private lemma ons_bucketESeries_eq_geometric_eq
  [Fintype E]
  [DecidableEq E]
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {x omega : ℂ}
  {e : ons_Dart L}
-- given
  (hsum : Summable fun s => ‖ons_firstReturnWeight (ons_KWmat L x omega) e (ons_dartRev L e) s‖)
  (hsmall : ∑' s, ‖ons_firstReturnWeight (ons_KWmat L x omega) e (ons_dartRev L e) s‖ < 1) :
-- imply
  (∑' n : ℕ, ons_bucketE L x omega e n / ((n : ℂ) + 1)) = ∑' k : ℕ, (∑' s, ons_firstReturnWeight (ons_KWmat L x omega) e (ons_dartRev L e) s) ^ (k + 1) / (k + 1) := by
-- proof
  apply StatMech.Onsager.ons_bucketESeries_eq_geometric x omega e hsum hsmall

/--
[ons_summable_bucketE_firstReturn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanBucketCancellation.lean)
-/
@[path]
private lemma ons_summable_bucketE_firstReturn_eq
  [Fintype E]
  [DecidableEq E]
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {x omega : ℂ}
  {e : ons_Dart L}
-- given
  (hsum : Summable fun s => ‖ons_firstReturnWeight (ons_KWmat L x omega) e (ons_dartRev L e) s‖)
  (hsmall : ∑' s, ‖ons_firstReturnWeight (ons_KWmat L x omega) e (ons_dartRev L e) s‖ < 1) :
-- imply
  Summable fun n : ℕ => ons_bucketE L x omega e n / ((n : ℂ) + 1) := by
-- proof
  apply StatMech.Onsager.ons_summable_bucketE_firstReturn x omega e hsum hsmall

/--
[ons_hlam_firstReturn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanBucketCancellation.lean)
-/
@[path]
private lemma ons_hlam_firstReturn_eq
  [Fintype E]
  [DecidableEq E]
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {x omega : ℂ}
  {e : ons_Dart L}
-- given
  (hsum : Summable fun s => ‖ons_firstReturnWeight (ons_KWmat L x omega) e (ons_dartRev L e) s‖)
  (hsmall : ∑' s, ‖ons_firstReturnWeight (ons_KWmat L x omega) e (ons_dartRev L e) s‖ < 1) :
-- imply
  Complex.exp (- ∑' n : ℕ, ons_bucketE L x omega e n / ((n : ℂ) + 1)) = 1 - ∑' s, ons_firstReturnWeight (ons_KWmat L x omega) e (ons_dartRev L e) s := by
-- proof
  apply StatMech.Onsager.ons_hlam_firstReturn x omega e hsum hsmall


-- created on 2026-10-23

import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.ShermanConvergence.Part2
open StatMech StatMech.Onsager


/--
[ons_sum_factorMajorant_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanConvergence.lean)
-/
@[path]
private lemma ons_sum_factorMajorant_length_eq
  [Fintype E]
  [DecidableEq E]
  {q : ℝ}
  {m : ℕ} :
-- imply
  (∑ f : Fin m → E, ons_factorMajorant q (List.ofFn f)) = if m < 2 then 0 else (Fintype.card E : ℝ) ^ m * q ^ (m - 1) := by
-- proof
  apply StatMech.Onsager.ons_sum_factorMajorant_length q m

/--
[ons_summable_factorMajorant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanConvergence.lean)
-/
@[path]
private lemma ons_summable_factorMajorant_eq
  [Fintype E]
  [DecidableEq E]
  {q : ℝ}
-- given
  (hq : 0 ≤ q)
  (hsmall : (Fintype.card E : ℝ) * q < 1) :
-- imply
  Summable (ons_factorMajorant q : List E → ℝ) := by
-- proof
  apply StatMech.Onsager.ons_summable_factorMajorant q hq hsmall

/--
[ons_tsum_factorMajorant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanConvergence.lean)
-/
@[path]
private lemma ons_tsum_factorMajorant_eq
  [Fintype E]
  [DecidableEq E]
  {q : ℝ}
-- given
  (hq : 0 ≤ q)
  (hsmall : (Fintype.card E : ℝ) * q < 1) :
-- imply
  (∑' s : List E, ons_factorMajorant q s) = (Fintype.card E : ℝ) ^ 2 * q / (1 - (Fintype.card E : ℝ) * q) := by
-- proof
  apply StatMech.Onsager.ons_tsum_factorMajorant q hq hsmall

/--
[norm_ons_edgeWeight_le_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanConvergence.lean)
-/
@[path]
private lemma norm_ons_edgeWeight_le_pow_eq
  [Fintype E]
  [DecidableEq E]
  {Lambda : Matrix E E ℂ}
  {q : ℝ}
  {s : List E}
-- given
  (hq : 0 ≤ q)
  (hentry : ∀ i j, ‖Lambda i j‖ ≤ q) :
-- imply
  ‖ons_edgeWeight Lambda s‖ ≤ q ^ (s.length - 1) := by
-- proof
  apply StatMech.Onsager.norm_ons_edgeWeight_le_pow Lambda q hq hentry s

/--
[norm_ons_firstReturnWeight_le_majorant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanConvergence.lean)
-/
@[path]
private lemma norm_ons_firstReturnWeight_le_majorant_eq
  [Fintype E]
  [DecidableEq E]
  {Lambda : Matrix E E ℂ}
  {e r : E}
  {q : ℝ}
  {s : List E}
-- given
  (hq : 0 ≤ q)
  (hentry : ∀ i j, ‖Lambda i j‖ ≤ q) :
-- imply
  ‖ons_firstReturnWeight Lambda e r s‖ ≤ ons_factorMajorant q s := by
-- proof
  apply StatMech.Onsager.norm_ons_firstReturnWeight_le_majorant Lambda e r q hq hentry s

/--
[ons_firstReturnWeight_converges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanConvergence.lean)
-/
@[path]
private lemma ons_firstReturnWeight_converges_eq
  [Fintype E]
  [DecidableEq E]
  {Lambda : Matrix E E ℂ}
  {e r : E}
  {q : ℝ}
-- given
  (hq : 0 ≤ q)
  (hentry : ∀ i j, ‖Lambda i j‖ ≤ q)
  (hcard : (Fintype.card E : ℝ) * q < 1) :
-- imply
  Summable fun s => ‖ons_firstReturnWeight Lambda e r s‖ := by
-- proof
  apply StatMech.Onsager.ons_firstReturnWeight_converges Lambda e r q hq hentry hcard

/--
[ons_tsum_norm_firstReturnWeight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanConvergence.lean)
-/
@[path]
private lemma ons_tsum_norm_firstReturnWeight_le_eq
  [Fintype E]
  [DecidableEq E]
  {Lambda : Matrix E E ℂ}
  {e r : E}
  {q : ℝ}
-- given
  (hq : 0 ≤ q)
  (hentry : ∀ i j, ‖Lambda i j‖ ≤ q)
  (hcard : (Fintype.card E : ℝ) * q < 1) :
-- imply
  (∑' s, ‖ons_firstReturnWeight Lambda e r s‖) ≤ (Fintype.card E : ℝ) ^ 2 * q / (1 - (Fintype.card E : ℝ) * q) := by
-- proof
  apply StatMech.Onsager.ons_tsum_norm_firstReturnWeight_le Lambda e r q hq hentry hcard

/--
[ons_firstReturnWeight_small](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanConvergence.lean)
-/
@[path]
private lemma ons_firstReturnWeight_small_eq
  [Fintype E]
  [DecidableEq E]
  {Lambda : Matrix E E ℂ}
  {e r : E}
  {q : ℝ}
-- given
  (hq : 0 ≤ q)
  (hentry : ∀ i j, ‖Lambda i j‖ ≤ q)
  (hsmall : q < (2 * (Fintype.card E : ℝ) ^ 2)⁻¹) :
-- imply
  Summable (fun s => ‖ons_firstReturnWeight Lambda e r s‖) ∧ (∑' s, ‖ons_firstReturnWeight Lambda e r s‖) < 1 := by
-- proof
  apply StatMech.Onsager.ons_firstReturnWeight_small Lambda e r q hq hentry hsmall

/--
[norm_ons_KWmat_turnRoot_entry_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanConvergence.lean)
-/
@[path]
private lemma norm_ons_KWmat_turnRoot_entry_le_eq
  [Fintype E]
  [DecidableEq E]
  {L : ℕ}
  {x : ℝ}
  {d2 d1 : ons_Dart L} :
-- imply
  ‖ons_KWmat L (x : ℂ) ons_turnRoot d2 d1‖ ≤ ‖(x : ℂ)‖ := by
-- proof
  apply StatMech.Onsager.norm_ons_KWmat_turnRoot_entry_le L x d2 d1

/--
[ons_ShermanRadius_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanConvergence.lean)
-/
@[path]
private lemma ons_ShermanRadius_pos_eq
  [Fintype E]
  [DecidableEq E]
  {L : ℕ}
  [NeZero L] :
-- imply
  0 < ons_ShermanRadius L := by
-- proof
  apply StatMech.Onsager.ons_ShermanRadius_pos L

/--
[ons_KW_firstReturnWeight_small](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanConvergence.lean)
-/
@[path]
private lemma ons_KW_firstReturnWeight_small_eq
  [Fintype E]
  [DecidableEq E]
  {L : ℕ}
  [NeZero L]
  {x : ℝ}
  {e : ons_Dart L}
-- given
  (hx : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L)) :
-- imply
  Summable (fun s => ‖ons_firstReturnWeight (ons_KWmat L (x : ℂ) ons_turnRoot) e (ons_dartRev L e) s‖) ∧ (∑' s, ‖ons_firstReturnWeight (ons_KWmat L (x : ℂ) ons_turnRoot) e (ons_dartRev L e) s‖) < 1 := by
-- proof
  apply StatMech.Onsager.ons_KW_firstReturnWeight_small L hx e

/--
[norm_ons_loopWeight_le_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanConvergence.lean)
-/
@[path]
private lemma norm_ons_loopWeight_le_pow_eq
  [Fintype E]
  [DecidableEq E]
  {Lambda : Matrix E E ℂ}
  {q : ℝ}
  {n : ℕ}
  [NeZero n]
  {v : Fin n → E}
-- given
  (hq : 0 ≤ q)
  (hentry : ∀ i j, ‖Lambda i j‖ ≤ q) :
-- imply
  ‖ons_loopWeight Lambda v‖ ≤ q ^ n := by
-- proof
  apply StatMech.Onsager.norm_ons_loopWeight_le_pow Lambda q hq hentry v

/--
[norm_filtered_loopSum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanConvergence.lean)
-/
@[path]
private lemma norm_filtered_loopSum_le_eq
  [Fintype E]
  [DecidableEq E]
  {Lambda : Matrix E E ℂ}
  {q : ℝ}
  {n : ℕ}
  [DecidablePred P]
-- given
  (hq : 0 ≤ q)
  (hentry : ∀ i j, ‖Lambda i j‖ ≤ q)
  (P : (Fin (n + 1) → E) → Prop) :
-- imply
  ‖∑ v ∈ Finset.univ.filter P, ons_loopWeight Lambda v‖ ≤ ((Fintype.card E : ℝ) * q) ^ (n + 1) := by
-- proof
  apply StatMech.Onsager.norm_filtered_loopSum_le Lambda q hq hentry n P

/--
[ons_summable_filteredLoopSeries](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanConvergence.lean)
-/
@[path]
private lemma ons_summable_filteredLoopSeries_eq
  [Fintype E]
  [DecidableEq E]
  {Lambda : Matrix E E ℂ}
  {q : ℝ}
  [∀ n, DecidablePred (P n)]
-- given
  (hq : 0 ≤ q)
  (hentry : ∀ i j, ‖Lambda i j‖ ≤ q)
  (hcard : (Fintype.card E : ℝ) * q < 1)
  (P : (n : ℕ) → (Fin (n + 1) → E) → Prop) :
-- imply
  Summable fun n : ℕ => (∑ v ∈ Finset.univ.filter (P n), ons_loopWeight Lambda v) / ((n : ℂ) + 1) := by
-- proof
  apply StatMech.Onsager.ons_summable_filteredLoopSeries Lambda q hq hentry hcard P

/--
[ons_Sherman_card_mul_small](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanConvergence.lean)
-/
@[path]
private lemma ons_Sherman_card_mul_small_eq
  [Fintype E]
  [DecidableEq E]
  {L : ℕ}
  [NeZero L]
  {x : ℝ}
-- given
  (hx : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L)) :
-- imply
  (Fintype.card (ons_Dart L) : ℝ) * ‖x‖ < 1 := by
-- proof
  apply StatMech.Onsager.ons_Sherman_card_mul_small L hx

/--
[ons_KWmat_eq_phase_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanConvergence.lean)
-/
@[path]
private lemma ons_KWmat_eq_phase_zero_eq
  [Fintype E]
  [DecidableEq E]
  {L : ℕ}
  {x omega : ℂ} :
-- imply
  ons_KWmat L x omega = ons_KWmatPhase L x omega (ons_spinPhase L 0) (ons_spinPhase L 0) := by
-- proof
  apply StatMech.Onsager.ons_KWmat_eq_phase_zero L x omega

/--
[ons_KWmat_spectral_Sherman_small](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanConvergence.lean)
-/
@[path]
private lemma ons_KWmat_spectral_Sherman_small_eq
  [Fintype E]
  [DecidableEq E]
  {L : ℕ}
  [NeZero L]
  {x : ℝ}
-- given
  (hx : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L)) :
-- imply
  ∀ alpha ∈ (ons_KWmat L (x : ℂ) ons_turnRoot).charpoly.roots, ‖alpha‖ < 1 := by
-- proof
  apply StatMech.Onsager.ons_KWmat_spectral_Sherman_small L hx

/--
[ons_summable_bucketN_Sherman_small](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanConvergence.lean)
-/
@[path]
private lemma ons_summable_bucketN_Sherman_small_eq
  [Fintype E]
  [DecidableEq E]
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {x : ℝ}
  {e : ons_Dart L}
-- given
  (hx : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L)) :
-- imply
  Summable fun n : ℕ => ons_bucketN L (x : ℂ) ons_turnRoot e n / ((n : ℂ) + 1) := by
-- proof
  apply StatMech.Onsager.ons_summable_bucketN_Sherman_small L hx e

/--
[ons_det_eq_A_mul_firstReturn_sq_Sherman_small](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanConvergence.lean)
-/
@[path]
private lemma ons_det_eq_A_mul_firstReturn_sq_Sherman_small_eq
  [Fintype E]
  [DecidableEq E]
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {x : ℝ}
  {e : ons_Dart L}
-- given
  (hx : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L)) :
-- imply
  (1 - ons_KWmat L (x : ℂ) ons_turnRoot).det = Complex.exp (- ∑' n : ℕ, ons_bucketN L (x : ℂ) ons_turnRoot e n / ((n : ℂ) + 1)) * (1 - ∑' s, ons_firstReturnWeight (ons_KWmat L (x : ℂ) ons_turnRoot) e (ons_dartRev L e) s) ^ 2 := by
-- proof
  apply StatMech.Onsager.ons_det_eq_A_mul_firstReturn_sq_Sherman_small L hx e


-- created on 2026-10-23

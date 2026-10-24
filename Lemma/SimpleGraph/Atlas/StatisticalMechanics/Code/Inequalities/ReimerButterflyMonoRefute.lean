import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Inequalities.ReimerButterflyMonoRefute
open MeasureTheory Finset StatMech


/--
[slice_disjointOccurrence_true_strong](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyMonoRefute.lean)
-/
@[path]
private lemma slice_disjointOccurrence_true_strong_eq
  {n : ℕ}
  {A B : Set (ConfigSpace (Fin (n + 1)))} :
-- imply
  slice (disjointOccurrence A B) true ⊆ disjointOccurrence (slice A true) (slice B true) := by
-- proof
  apply StatMech.slice_disjointOccurrence_true_strong

/--
[wprob_slice_false_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyMonoRefute.lean)
-/
@[path]
private lemma wprob_slice_false_le_eq
  {n : ℕ}
  {ψ : Fin n → Bool → ℝ}
  {A B : Set (ConfigSpace (Fin (n + 1)))}
-- given
  (hψ0 : ∀ i b, 0 ≤ ψ i b) :
-- imply
  wprob ψ (slice (disjointOccurrence A B) false) ≤ wprob ψ (disjointOccurrence (slice A false) (slice B false)) := by
-- proof
  apply StatMech.wprob_slice_false_le ψ hψ0 A B

/--
[wprob_slice_true_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyMonoRefute.lean)
-/
@[path]
private lemma wprob_slice_true_le_eq
  {n : ℕ}
  {ψ : Fin n → Bool → ℝ}
  {A B : Set (ConfigSpace (Fin (n + 1)))}
-- given
  (hψ0 : ∀ i b, 0 ≤ ψ i b) :
-- imply
  wprob ψ (slice (disjointOccurrence A B) true) ≤ wprob ψ (disjointOccurrence (slice A true) (slice B true)) := by
-- proof
  apply StatMech.wprob_slice_true_le ψ hψ0 A B

/--
[refuteW_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyMonoRefute.lean)
-/
@[path]
private lemma refuteW_nonneg_eq :
-- imply
  ∀ i b, 0 ≤ refuteW i b := by
-- proof
  apply StatMech.refuteW_nonneg

/--
[refuteW_prob](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyMonoRefute.lean)
-/
@[path]
private lemma refuteW_prob_eq :
-- imply
  ∀ i, refuteW i false + refuteW i true = 1 := by
-- proof
  apply StatMech.refuteW_prob

/--
[slice_refuteA_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyMonoRefute.lean)
-/
@[path]
private lemma slice_refuteA_true_eq :
-- imply
  slice refuteA true = (∅ : Set (ConfigSpace (Fin 1))) := by
-- proof
  apply StatMech.slice_refuteA_true

/--
[wprob_empty_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyMonoRefute.lean)
-/
@[path]
private lemma wprob_empty_one_eq
  {φ : Fin 1 → Bool → ℝ} :
-- imply
  wprob φ (∅ : Set (ConfigSpace (Fin 1))) = 0 := by
-- proof
  apply StatMech.wprob_empty_one φ

/--
[wprob_pos_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyMonoRefute.lean)
-/
@[path]
private lemma wprob_pos_of_mem_eq
  {S : Set (ConfigSpace (Fin 1))}
-- given
  (hmem : refuteTail ∈ S) :
-- imply
  0 < wprob refuteW S := by
-- proof
  apply StatMech.wprob_pos_of_mem S hmem

/--
[refuteTail_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyMonoRefute.lean)
-/
@[path]
private lemma refuteTail_mem_box_eq :
-- imply
  refuteTail ∈ disjointOccurrence (slice refuteA false) (slice refuteB true) := by
-- proof
  apply StatMech.refuteTail_mem_box

/--
[reimerSliceStep_one_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyMonoRefute.lean)
-/
@[path]
private lemma reimerSliceStep_one_false_eq :
-- imply
  ¬ ReimerSliceStep 1 := by
-- proof
  apply StatMech.reimerSliceStep_one_false

/--
[slice_recombination_gap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyMonoRefute.lean)
-/
@[path]
private lemma slice_recombination_gap_eq
  {a0 a1 b0 b1 p q : ℝ}
-- given
  (hqp : q + p = 1) :
-- imply
  (q * a0 + p * a1) * (q * b0 + p * b1) - (q * (a0 * b0) + p * (a1 * b1)) = - (q * p * ((a0 - a1) * (b0 - b1))) := by
-- proof
  apply StatMech.slice_recombination_gap a0 a1 b0 b1 p q hqp

/--
[slice_cross_sign_can_be_positive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyMonoRefute.lean)
-/
@[path]
private lemma slice_cross_sign_can_be_positive_eq :
-- imply
  ∃ (a0 a1 b0 b1 : ℝ), 0 < (a0 - a1) * (b0 - b1) := by
-- proof
  apply StatMech.slice_cross_sign_can_be_positive


-- created on 2026-10-23

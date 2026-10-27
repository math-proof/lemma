import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.StateWeightedDeletion
open StatMech StatMech.Onsager


/--
[ons_matrixLoopSum_orientation_symm_of_loopRev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/StateWeightedDeletion.lean)
-/
@[path]
private lemma ons_matrixLoopSum_orientation_symm_of_loopRev_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {rev : E → E}
  {M : Matrix E E ℂ}
  {e : E}
-- given
  (hrev : Function.Involutive rev)
  (hloopRev : ∀ loop : Fin n → E, ons_loopWeight M (ons_involutiveLoopRev rev loop) = ons_loopWeight M loop) :
-- imply
  (∑ loop ∈ Finset.univ.filter (fun loop : Fin n → E ↦ (∃ i, loop i = e) ∧ ¬ ∃ j, loop j = rev e), ons_loopWeight M loop) = ∑ loop ∈ Finset.univ.filter (fun loop : Fin n → E ↦ (∃ i, loop i = rev e) ∧ ¬ ∃ j, loop j = e), ons_loopWeight M loop := by
-- proof
  apply StatMech.Onsager.ons_matrixLoopSum_orientation_symm_of_loopRev rev hrev M hloopRev e

/--
[ons_matrixLoopSum_two_bucket](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/StateWeightedDeletion.lean)
-/
@[path]
private lemma ons_matrixLoopSum_two_bucket_eq
  [Fintype E]
  [DecidableEq E]
  {M : Matrix E E ℂ}
  {e r : E}
  {n : ℕ}
-- given
  (hboth : (∑ loop ∈ ons_loopSetBoth (n := n + 1) e r, ons_loopWeight M loop) = 0)
  (hsymm : (∑ loop ∈ Finset.univ.filter (fun loop : Fin (n + 1) → E ↦ (∃ i, loop i = e) ∧ ¬ ∃ j, loop j = r), ons_loopWeight M loop) = ∑ loop ∈ Finset.univ.filter (fun loop : Fin (n + 1) → E ↦ (∃ i, loop i = r) ∧ ¬ ∃ j, loop j = e), ons_loopWeight M loop) :
-- imply
  (∑ loop : Fin (n + 1) → E, ons_loopWeight M loop) = 2 * ons_matrixBucketE M e r n + ons_matrixBucketN M e r n := by
-- proof
  apply StatMech.Onsager.ons_matrixLoopSum_two_bucket M e r n hboth hsymm

/--
[ons_detWalkRoot_matrix_delete_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/StateWeightedDeletion.lean)
-/
@[path]
private lemma ons_detWalkRoot_matrix_delete_pair_eq
  [Fintype E]
  [DecidableEq E]
  {M : Matrix E E ℂ}
  {e r : E}
  {q : ℝ}
-- given
  (her : e ≠ r)
  (hq : 0 ≤ q)
  (hentry : ∀ x y, ‖M x y‖ ≤ q)
  (hsmall : q < (2 * (Fintype.card E : ℝ) ^ 2)⁻¹)
  (hcard : (Fintype.card E : ℝ) * q < 1)
  (hboth : ∀ n : ℕ, (∑ loop ∈ ons_loopSetBoth (n := n + 1) e r, ons_loopWeight M loop) = 0)
  (hsymm : ∀ n : ℕ, (∑ loop ∈ Finset.univ.filter (fun loop : Fin (n + 1) → E ↦ (∃ i, loop i = e) ∧ ¬ ∃ j, loop j = r), ons_loopWeight M loop) = ∑ loop ∈ Finset.univ.filter (fun loop : Fin (n + 1) → E ↦ (∃ i, loop i = r) ∧ ¬ ∃ j, loop j = e), ons_loopWeight M loop) :
-- imply
  ons_detWalkRoot M = ons_detWalkRoot (ons_maskMatrix ({e, r} : Finset E) M) * (1 - ∑' s, ons_firstReturnWeight M e r s) := by
-- proof
  apply StatMech.Onsager.ons_detWalkRoot_matrix_delete_pair M e r her q hq hentry hsmall hcard hboth hsymm

/--
[ons_detWalkRoot_norm_sub_one_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/StateWeightedDeletion.lean)
-/
@[path]
private lemma ons_detWalkRoot_norm_sub_one_lt_one_eq
  [Fintype E]
  [DecidableEq E]
  {M : Matrix E E ℂ}
  {q : ℝ}
-- given
  (hq : 0 ≤ q)
  (hentry : ∀ x y, ‖M x y‖ ≤ q)
  (hcard : (Fintype.card E : ℝ) * q < 1)
  (hgeom : (∑' n : ℕ, ((Fintype.card E : ℝ) * q) ^ (n + 1)) < 1) :
-- imply
  ‖ons_detWalkRoot M - 1‖ < 1 := by
-- proof
  apply StatMech.Onsager.ons_detWalkRoot_norm_sub_one_lt_one M q hq hentry hcard hgeom

/--
[ons_geom_sum_lt_one_of_Sherman_small](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/StateWeightedDeletion.lean)
-/
@[path]
private lemma ons_geom_sum_lt_one_of_Sherman_small_eq
  [Fintype E]
  [Nonempty E]
  {q : ℝ}
-- given
  (hq : 0 ≤ q)
  (hsmall : q < (2 * (Fintype.card E : ℝ) ^ 2)⁻¹) :
-- imply
  (∑' n : ℕ, ((Fintype.card E : ℝ) * q) ^ (n + 1)) < 1 := by
-- proof
  apply StatMech.Onsager.ons_geom_sum_lt_one_of_Sherman_small q hq hsmall

/--
[ons_eq_of_sq_eq_sq_of_norm_sub_one_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/StateWeightedDeletion.lean)
-/
@[path]
private lemma ons_eq_of_sq_eq_sq_of_norm_sub_one_lt_one_eq
  {x y : ℂ}
-- given
  (hsq : x ^ 2 = y ^ 2)
  (hx : ‖x - 1‖ < 1)
  (hy : ‖y - 1‖ < 1) :
-- imply
  x = y := by
-- proof
  apply StatMech.Onsager.ons_eq_of_sq_eq_sq_of_norm_sub_one_lt_one x y hsq hx hy

/--
[ons_detWalkRoot_eq_of_det_eq_of_small](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/StateWeightedDeletion.lean)
-/
@[path]
private lemma ons_detWalkRoot_eq_of_det_eq_of_small_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype F]
  [DecidableEq F]
  {M : Matrix E E ℂ}
  {N : Matrix F F ℂ}
  {qM qN : ℝ}
-- given
  (hqM : 0 ≤ qM)
  (hqN : 0 ≤ qN)
  (hentryM : ∀ x y, ‖M x y‖ ≤ qM)
  (hentryN : ∀ x y, ‖N x y‖ ≤ qN)
  (hcardM : (Fintype.card E : ℝ) * qM < 1)
  (hcardN : (Fintype.card F : ℝ) * qN < 1)
  (hgeomM : (∑' n : ℕ, ((Fintype.card E : ℝ) * qM) ^ (n + 1)) < 1)
  (hgeomN : (∑' n : ℕ, ((Fintype.card F : ℝ) * qN) ^ (n + 1)) < 1)
  (hdet : (1 - M).det = (1 - N).det) :
-- imply
  ons_detWalkRoot M = ons_detWalkRoot N := by
-- proof
  apply StatMech.Onsager.ons_detWalkRoot_eq_of_det_eq_of_small M N qM qN hqM hqN hentryM hentryN hcardM hcardN hgeomM hgeomN hdet


-- created on 2026-10-23

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanPhaseAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.KWPhaseLemma5
import Theorem.StatisticalMechanics.Code.Onsager.KWSpectral.Part2
import Def.StatisticalMechanics.Code.Onsager.ShermanPhaseAssembly.Part3


namespace StatMech.Onsager

open Matrix BigOperators

theorem ons_phaseAvoidRoot_eq_maskRoot
    (L : ℕ) [NeZero L] (x : ℝ) (a b : Fin 2)
    (e : ons_Dart L) :
    ons_phaseAvoidRoot L x a b e =
      ons_detWalkRoot
        (ons_maskMatrix ({e, ons_dartRev L e} : Finset (ons_Dart L))
          (ons_KWmatPhase L (x : ℂ) ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b))) := by
  let M := ons_KWmatPhase L (x : ℂ) ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b)
  let S : Finset (ons_Dart L) := {e, ons_dartRev L e}
  have hterm : ∀ n : ℕ,
      (∑ d : Fin (n + 1) → ons_Dart L,
        ∏ k : Fin (n + 1), (ons_maskMatrix S M) (d k) (d (k + 1))) =
      ons_phaseBucketN L (x : ℂ) ons_turnRoot a b e n := by
    intro n
    have hsum := ons_loopSum_maskMatrix (n := n + 1) S M
    have hset :
        Finset.univ.filter (fun d : Fin (n + 1) → ons_Dart L =>
          ¬ ∃ k, d k ∈ S) =
        Finset.univ.filter (fun d : Fin (n + 1) → ons_Dart L =>
          ¬ (∃ i, d i = e) ∧ ¬ (∃ j, d j = ons_dartRev L e)) := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, S,
        Finset.mem_insert, Finset.mem_singleton]
      aesop
    rw [hset] at hsum
    simpa only [M, S, ons_loopWeight, ons_phaseBucketN] using hsum
  unfold ons_phaseAvoidRoot ons_detWalkRoot
  apply congrArg Complex.exp
  congr 1
  apply congrArg Neg.neg
  apply tsum_congr
  intro n
  exact congrArg (· / ((n : ℂ) + 1)) (hterm n).symm


theorem ons_spinWalkRoot_factor_firstReturn_small
    (L : ℕ) [NeZero L] [Fact (2 < L)]
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L))
    (a b : Fin 2) (e : ons_Dart L) :
    ons_spinWalkRoot L x a b = ons_phaseAvoidRoot L x a b e *
      (1 - ∑' s, ons_firstReturnWeight
        (ons_KWmatPhase L (x : ℂ) ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b))
        e (ons_dartRev L e) s) := by
  have hfirst := ons_KWmatPhase_firstReturnWeight_small L hx a b e
    (ons_dartRev L e)
  have hB := ons_summable_phaseBucketE_firstReturn
    (x : ℂ) ons_turnRoot a b e hfirst.1 hfirst.2
  let Q : (n : ℕ) → (Fin (n + 1) → ons_Dart L) → Prop := fun _ d =>
    ¬ (∃ i, d i = e) ∧ ¬ (∃ j, d j = ons_dartRev L e)
  have hNraw := ons_KWmatPhase_filteredLoopSeries_summable L hx a b Q
  have hN : Summable fun n : ℕ =>
      ons_phaseBucketN L (x : ℂ) ons_turnRoot a b e n /
        ((n : ℂ) + 1) := by
    simpa only [ons_phaseBucketN, Q] using hNraw
  have hseries :
      (∑' n : ℕ,
        (∑ d : Fin (n + 1) → ons_Dart L,
          ∏ k : Fin (n + 1),
            ons_KWmatPhase L (x : ℂ) ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b)
              (d k) (d (k + 1))) / ((n : ℂ) + 1)) =
      2 * (∑' n : ℕ,
        ons_phaseBucketE L (x : ℂ) ons_turnRoot a b e n /
          ((n : ℂ) + 1)) +
      (∑' n : ℕ,
        ons_phaseBucketN L (x : ℂ) ons_turnRoot a b e n /
          ((n : ℂ) + 1)) := by
    have hterm : ∀ n : ℕ,
        (∑ d : Fin (n + 1) → ons_Dart L,
          ∏ k : Fin (n + 1),
            ons_KWmatPhase L (x : ℂ) ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b)
              (d k) (d (k + 1))) =
        2 * ons_phaseBucketE L (x : ℂ) ons_turnRoot a b e n +
          ons_phaseBucketN L (x : ℂ) ons_turnRoot a b e n := by
      intro n
      simpa only [ons_loopWeight] using
        (ons_KWmatPhase_loopSum_two_bucket
          (L := L) (n := n) (x : ℂ) ons_turnRoot
          ons_turnRoot_sq a b e)
    rw [tsum_congr (fun n : ℕ =>
      congrArg (· / ((n : ℂ) + 1)) (hterm n))]
    have heq : (fun n : ℕ =>
        (2 * ons_phaseBucketE L (x : ℂ) ons_turnRoot a b e n +
          ons_phaseBucketN L (x : ℂ) ons_turnRoot a b e n) /
            ((n : ℂ) + 1)) =
        (fun n : ℕ => 2 *
          (ons_phaseBucketE L (x : ℂ) ons_turnRoot a b e n /
            ((n : ℂ) + 1)) +
          ons_phaseBucketN L (x : ℂ) ons_turnRoot a b e n /
            ((n : ℂ) + 1)) := by
      funext n
      ring
    rw [heq, (hB.mul_left 2).tsum_add hN, tsum_mul_left]
  rw [ons_spinWalkRoot, ons_detWalkRoot, hseries]
  rw [show -(2 * (∑' n : ℕ,
        ons_phaseBucketE L (x : ℂ) ons_turnRoot a b e n /
          ((n : ℂ) + 1)) +
      (∑' n : ℕ,
        ons_phaseBucketN L (x : ℂ) ons_turnRoot a b e n /
          ((n : ℂ) + 1))) / 2 =
      (-(∑' n : ℕ,
        ons_phaseBucketN L (x : ℂ) ons_turnRoot a b e n /
          ((n : ℂ) + 1)) / 2) +
      (-(∑' n : ℕ,
        ons_phaseBucketE L (x : ℂ) ons_turnRoot a b e n /
          ((n : ℂ) + 1))) by ring,
    Complex.exp_add]
  rw [ons_hlam_spinPhase_firstReturn
    (x : ℂ) ons_turnRoot a b e hfirst.1 hfirst.2]
  rfl

theorem ons_summable_phaseBucketN_Sherman_small
    (L : ℕ) [NeZero L] [Fact (2 < L)]
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L))
    (a b : Fin 2) (e : ons_Dart L) :
    Summable fun n : ℕ =>
      ons_phaseBucketN L (x : ℂ) ons_turnRoot a b e n /
        ((n : ℂ) + 1) := by
  let P : (n : ℕ) → (Fin (n + 1) → ons_Dart L) → Prop := fun _ d =>
    ¬ (∃ i, d i = e) ∧ ¬ (∃ j, d j = ons_dartRev L e)
  have hs := ons_KWmatPhase_filteredLoopSeries_summable L hx a b P
  simpa only [ons_phaseBucketN, P] using hs


theorem ons_detWalkRoot_mask_delete_pair
    (L : ℕ) [NeZero L] [Fact (2 < L)]
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L))
    (a b : Fin 2) (forbidden : Finset (ons_Dart L))
    (hforbidden : ∀ d,
      ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden)
    (e : ons_Dart L) :
    ons_detWalkRoot
        (ons_maskMatrix forbidden
          (ons_KWmatPhase L (x : ℂ) ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b))) =
      ons_detWalkRoot
          (ons_maskMatrix
            (({e, ons_dartRev L e} : Finset (ons_Dart L)) ∪ forbidden)
            (ons_KWmatPhase L (x : ℂ) ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b))) *
        (1 - ∑' s, ons_firstReturnWeight
          (ons_maskMatrix forbidden
            (ons_KWmatPhase L (x : ℂ) ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b)))
          e (ons_dartRev L e) s) := by
  let M := ons_KWmatPhase L (x : ℂ) ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b)
  let MF := ons_maskMatrix forbidden M
  let pair : Finset (ons_Dart L) := {e, ons_dartRev L e}
  have hentry : ∀ d2 d1 : ons_Dart L, ‖MF d2 d1‖ ≤ ‖(x : ℂ)‖ := by
    intro d2 d1
    simp only [MF, ons_maskMatrix]
    split
    · simp
    · exact norm_ons_KWmatPhase_spin_entry_le L x a b d2 d1
  have hfirst :
      Summable (fun s =>
        ‖ons_firstReturnWeight MF e (ons_dartRev L e) s‖) ∧
      (∑' s, ‖ons_firstReturnWeight MF e (ons_dartRev L e) s‖) < 1 := by
    apply ons_firstReturnWeight_small MF e (ons_dartRev L e)
      ‖(x : ℂ)‖ (norm_nonneg _) hentry
    simpa [ons_ShermanRadius, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hx.1] using hx.2
  have her : e ≠ ons_dartRev L e := (ons_dartRev_ne L e).symm
  have hB : Summable fun n : ℕ =>
      ons_maskPhaseBucketE L (x : ℂ) ons_turnRoot a b forbidden e n /
        ((n : ℂ) + 1) := by
    simpa only [ons_maskPhaseBucketE, MF, not_exists] using
      ons_summable_loopBucketSeries MF e (ons_dartRev L e)
        her hfirst.1 hfirst.2
  have hN : Summable fun n : ℕ =>
      ons_maskPhaseBucketN L (x : ℂ) ons_turnRoot a b forbidden e n /
        ((n : ℂ) + 1) := by
    let P : (n : ℕ) → (Fin (n + 1) → ons_Dart L) → Prop := fun _ d =>
      ¬ (∃ i, d i = e) ∧ ¬ (∃ j, d j = ons_dartRev L e)
    have hs := ons_summable_filteredLoopSeries MF ‖(x : ℂ)‖
      (norm_nonneg _) hentry
      (by simpa [Complex.norm_real] using ons_Sherman_card_mul_small L hx) P
    simpa only [ons_maskPhaseBucketN, MF, P] using hs
  have hseries :
      (∑' n : ℕ,
        (∑ d : Fin (n + 1) → ons_Dart L,
          ons_loopWeight MF d) / ((n : ℂ) + 1)) =
      2 * (∑' n : ℕ,
        ons_maskPhaseBucketE L (x : ℂ) ons_turnRoot a b forbidden e n /
          ((n : ℂ) + 1)) +
      (∑' n : ℕ,
        ons_maskPhaseBucketN L (x : ℂ) ons_turnRoot a b forbidden e n /
          ((n : ℂ) + 1)) := by
    rw [tsum_congr (fun n : ℕ => congrArg (· / ((n : ℂ) + 1))
      (ons_KWmatPhase_mask_loopSum_two_bucket
        (L := L) (n := n) (x : ℂ) ons_turnRoot ons_turnRoot_sq
        a b forbidden hforbidden e))]
    have heq : (fun n : ℕ =>
        (2 * ons_maskPhaseBucketE L (x : ℂ) ons_turnRoot a b forbidden e n +
          ons_maskPhaseBucketN L (x : ℂ) ons_turnRoot a b forbidden e n) /
            ((n : ℂ) + 1)) =
        (fun n : ℕ => 2 *
          (ons_maskPhaseBucketE L (x : ℂ) ons_turnRoot a b forbidden e n /
            ((n : ℂ) + 1)) +
          ons_maskPhaseBucketN L (x : ℂ) ons_turnRoot a b forbidden e n /
            ((n : ℂ) + 1)) := by
      funext n
      ring
    rw [heq, (hB.mul_left 2).tsum_add hN, tsum_mul_left]
  have hlam :
      Complex.exp (-(∑' n : ℕ,
        ons_maskPhaseBucketE L (x : ℂ) ons_turnRoot a b forbidden e n /
          ((n : ℂ) + 1))) =
      1 - ∑' s, ons_firstReturnWeight MF e (ons_dartRev L e) s := by
    let z := ∑' s, ons_firstReturnWeight MF e (ons_dartRev L e) s
    have hz : ‖z‖ < 1 :=
      lt_of_le_of_lt (norm_tsum_le_tsum_norm hfirst.1) hfirst.2
    have hgeom := ons_loopBucketSeries_eq_geometric
      MF e (ons_dartRev L e) her hfirst.1 hfirst.2
    rw [show (∑' n : ℕ,
        ons_maskPhaseBucketE L (x : ℂ) ons_turnRoot a b forbidden e n /
          ((n : ℂ) + 1)) =
        ∑' k : ℕ, z ^ (k + 1) / (k + 1) by
      simpa only [ons_maskPhaseBucketE, MF, not_exists, z] using hgeom]
    exact ons_lemma4_exp hz
  have hNroot :
      Complex.exp (-(∑' n : ℕ,
        ons_maskPhaseBucketN L (x : ℂ) ons_turnRoot a b forbidden e n /
          ((n : ℂ) + 1)) / 2) =
      ons_detWalkRoot (ons_maskMatrix (pair ∪ forbidden) M) := by
    have hmask : ons_maskMatrix pair MF =
        ons_maskMatrix (pair ∪ forbidden) M := by
      simp only [MF]
      exact ons_maskMatrix_union pair forbidden M
    rw [← hmask]
    unfold ons_detWalkRoot
    apply congrArg Complex.exp
    congr 1
    apply congrArg Neg.neg
    apply tsum_congr
    intro n
    apply congrArg (· / ((n : ℂ) + 1))
    have hsum := ons_loopSum_maskMatrix (n := n + 1) pair MF
    have hset :
        Finset.univ.filter (fun d : Fin (n + 1) → ons_Dart L =>
          ¬ ∃ k, d k ∈ pair) =
        Finset.univ.filter (fun d : Fin (n + 1) → ons_Dart L =>
          ¬ (∃ i, d i = e) ∧ ¬ (∃ j, d j = ons_dartRev L e)) := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, pair,
        Finset.mem_insert, Finset.mem_singleton]
      aesop
    rw [hset] at hsum
    simpa only [ons_loopWeight, ons_maskPhaseBucketN, MF] using hsum.symm
  change ons_detWalkRoot MF =
    ons_detWalkRoot (ons_maskMatrix (pair ∪ forbidden) M) *
      (1 - ∑' s, ons_firstReturnWeight MF e (ons_dartRev L e) s)
  change Complex.exp (-(∑' n : ℕ,
      (∑ d : Fin (n + 1) → ons_Dart L,
        ∏ k : Fin (n + 1), MF (d k) (d (k + 1))) /
          ((n : ℂ) + 1)) / 2) =
    ons_detWalkRoot (ons_maskMatrix (pair ∪ forbidden) M) *
      (1 - ∑' s, ons_firstReturnWeight MF e (ons_dartRev L e) s)
  simp only [ons_loopWeight] at hseries
  rw [hseries]
  rw [show -(2 * (∑' n : ℕ,
        ons_maskPhaseBucketE L (x : ℂ) ons_turnRoot a b forbidden e n /
          ((n : ℂ) + 1)) +
      (∑' n : ℕ,
        ons_maskPhaseBucketN L (x : ℂ) ons_turnRoot a b forbidden e n /
          ((n : ℂ) + 1))) / 2 =
      (-(∑' n : ℕ,
        ons_maskPhaseBucketN L (x : ℂ) ons_turnRoot a b forbidden e n /
          ((n : ℂ) + 1)) / 2) +
      (-(∑' n : ℕ,
        ons_maskPhaseBucketE L (x : ℂ) ons_turnRoot a b forbidden e n /
          ((n : ℂ) + 1))) by ring,
    Complex.exp_add, hNroot, hlam]

end StatMech.Onsager

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
import Def.StatisticalMechanics.Code.Onsager.ShermanPhaseAssembly.Part5


namespace StatMech.Onsager

open Matrix BigOperators

theorem ons_subset_maskAfter (L : ℕ)
    (forbidden : Finset (ons_Dart L)) (es : List (ons_Dart L)) :
    forbidden ⊆ ons_maskAfter L forbidden es := by
  induction es generalizing forbidden with
  | nil => exact Finset.Subset.rfl
  | cons e es ih =>
      intro d hd
      apply ih (forbidden := ons_addDartPair L forbidden e)
      exact Finset.mem_union_right _ hd

theorem ons_mem_maskAfter_of_mem_list (L : ℕ)
    (forbidden : Finset (ons_Dart L)) (es : List (ons_Dart L))
    {d : ons_Dart L} (hd : d ∈ es) :
    d ∈ ons_maskAfter L forbidden es := by
  induction es generalizing forbidden with
  | nil => simp at hd
  | cons e es ih =>
      rw [List.mem_cons] at hd
      rcases hd with hd | hd
      · apply ons_subset_maskAfter L (ons_addDartPair L forbidden e) es
        simp [ons_addDartPair, hd]
      · exact ih (forbidden := ons_addDartPair L forbidden e) hd

theorem ons_detWalkRoot_mask_eliminate_list
    (L : ℕ) [NeZero L] [Fact (2 < L)]
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L))
    (a b : Fin 2) (forbidden : Finset (ons_Dart L))
    (hforbidden : ∀ d,
      ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden)
    (es : List (ons_Dart L)) :
    ons_detWalkRoot
        (ons_maskMatrix forbidden
          (ons_KWmatPhase L (x : ℂ) ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b))) =
      ons_detWalkRoot
          (ons_maskMatrix (ons_maskAfter L forbidden es)
            (ons_KWmatPhase L (x : ℂ) ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b))) *
        ons_maskEliminationProduct L x a b forbidden es := by
  induction es generalizing forbidden with
  | nil => simp [ons_maskAfter, ons_maskEliminationProduct]
  | cons e es ih =>
      have hdel := ons_detWalkRoot_mask_delete_pair L hx a b forbidden
        hforbidden e
      have hclosed : ∀ d,
          ons_dartRev L d ∈ ons_addDartPair L forbidden e ↔
            d ∈ ons_addDartPair L forbidden e :=
        ons_addDartPair_rev_closed L forbidden hforbidden e
      have hrest := ih (forbidden := ons_addDartPair L forbidden e) hclosed
      have hrest' := hrest
      simp only [ons_addDartPair] at hrest'
      rw [hdel, hrest']
      simp only [ons_maskAfter, ons_maskEliminationProduct, ons_addDartPair]
      ring


theorem ons_spinWalkRoot_eq_eliminationProduct
    (L : ℕ) [NeZero L] [Fact (2 < L)]
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L))
    (a b : Fin 2) :
    ons_spinWalkRoot L x a b =
      ons_maskEliminationProduct L x a b ∅
        (Finset.univ : Finset (ons_Dart L)).toList := by
  let es := (Finset.univ : Finset (ons_Dart L)).toList
  have hclosed : ∀ d : ons_Dart L,
      ons_dartRev L d ∈ (∅ : Finset (ons_Dart L)) ↔
        d ∈ (∅ : Finset (ons_Dart L)) := by simp
  have hiter := ons_detWalkRoot_mask_eliminate_list
    L hx a b (∅ : Finset (ons_Dart L)) hclosed es
  have hall : ons_maskAfter L (∅ : Finset (ons_Dart L)) es =
      (Finset.univ : Finset (ons_Dart L)) := by
    apply Finset.eq_univ_of_forall
    intro d
    apply ons_mem_maskAfter_of_mem_list L
      (∅ : Finset (ons_Dart L)) es
    simp [es]
  have hzero :
      ons_maskMatrix (Finset.univ : Finset (ons_Dart L))
        (ons_KWmatPhase L (x : ℂ) ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)) = 0 := by
    ext d2 d1
    simp [ons_maskMatrix]
  rw [hall, hzero, ons_detWalkRoot_zero, one_mul] at hiter
  simpa [ons_spinWalkRoot, ons_maskMatrix, es] using hiter


theorem ons_KWmatPhase_det_eq_A_mul_firstReturn_sq_Sherman_small
    (L : ℕ) [NeZero L] [Fact (2 < L)]
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L))
    (a b : Fin 2) (e : ons_Dart L) :
    (1 - ons_KWmatPhase L (x : ℂ) ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b)).det =
      Complex.exp (-∑' n : ℕ,
        ons_phaseBucketN L (x : ℂ) ons_turnRoot a b e n /
          ((n : ℂ) + 1)) *
      (1 - ∑' s, ons_firstReturnWeight
        (ons_KWmatPhase L (x : ℂ) ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b))
        e (ons_dartRev L e) s) ^ 2 := by
  have hfirst := ons_KWmatPhase_firstReturnWeight_small L hx a b e
    (ons_dartRev L e)
  have hB := ons_summable_phaseBucketE_firstReturn
    (x : ℂ) ons_turnRoot a b e hfirst.1 hfirst.2
  have hN := ons_summable_phaseBucketN_Sherman_small L hx a b e
  rw [ons_KWmatPhase_det_eq_A_mul_bucket (x : ℂ) ons_turnRoot
    ons_turnRoot_sq a b e
    (ons_KWmatPhase_spectral_Sherman_small L hx a b) hB hN]
  congr 1
  rw [pow_two, ← ons_hlam_spinPhase_firstReturn
    (x : ℂ) ons_turnRoot a b e hfirst.1 hfirst.2,
    ← Complex.exp_add]
  congr 1
  ring

end StatMech.Onsager

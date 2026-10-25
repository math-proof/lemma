/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/PerOrbitCardClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerSwapInjClose.Part3
import Def.StatisticalMechanics.Code.Inequalities.PerOrbitCardClose.Part7
open Finset MeasureTheory
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem poc_witnessInjection_rbi_false : ¬ poc_WitnessInjection rbi_A rbi_B := by
  rintro ⟨W, hinj⟩
  have hp1 : poc_rbi_p1.1 ∈ disjointOccurrence rbi_A rbi_B := rbi_FF_in_box
  have hp2 : poc_rbi_p2.1 ∈ disjointOccurrence rbi_A rbi_B := rbi_FT_in_box
  have hwLFF0 : W.wL (rbi_cfg false false) 0 = true :=
    poc_rbi_Bwit_FF _ (W.occB _ rbi_FF_in_box)
  have hwKFF0 : W.wK (rbi_cfg false false) 0 = false := by
    cases hw : W.wK (rbi_cfg false false) 0 with
    | false => rfl
    | true => rw [W.disj _ rbi_FF_in_box 0 hw] at hwLFF0; exact absurd hwLFF0 (by simp)
  have hwKFF1 : W.wK (rbi_cfg false false) 1 = true :=
    poc_rbi_Awit_FF_one _ (W.occA _ rbi_FF_in_box) hwKFF0
  have hwKFT0 : W.wK (rbi_cfg false true) 0 = true :=
    poc_rbi_Awit_FT_zero _ (W.occA _ rbi_FT_in_box)
  have hwLFT0 : W.wL (rbi_cfg false true) 0 = false := W.disj _ rbi_FT_in_box 0 hwKFT0
  have hwLFT1 : W.wL (rbi_cfg false true) 1 = true :=
    poc_rbi_Bwit_FT _ (W.occB _ rbi_FT_in_box) hwLFT0
  have hwKFT1 : W.wK (rbi_cfg false true) 1 = false := by
    cases hw : W.wK (rbi_cfg false true) 1 with
    | false => rfl
    | true => rw [W.disj _ rbi_FT_in_box 1 hw] at hwLFT1; exact absurd hwLFT1 (by simp)
  have hcol : swapPair (poc_swapSel rbi_A rbi_B W) poc_rbi_p1
      = swapPair (poc_swapSel rbi_A rbi_B W) poc_rbi_p2 := by
    apply Prod.ext <;> funext a <;> fin_cases a <;>
      simp only [swapPair_fst, swapPair_snd, poc_swapSel, swapGlue_apply, poc_rbi_p1, poc_rbi_p2,
        Fin.mk_zero, Fin.mk_one, rbi_cfg_zero, rbi_cfg_one, Fin.isValue,
        hwKFF0, hwKFF1, hwKFT0, hwKFT1, Bool.not_true, Bool.not_false] <;> rfl
  have heq : poc_rbi_p1 = poc_rbi_p2 := hinj hp1 hp2 hcol
  have hne : poc_rbi_p1 ≠ poc_rbi_p2 := by
    intro h
    have h2 := congrArg (fun q => q.1 1) h
    simp only [poc_rbi_p1, poc_rbi_p2, rbi_cfg_one] at h2
    exact absurd h2 (by decide)
  exact hne heq


theorem poc_slabCard_of_disjoint_support {A B : Set (ConfigSpace α)} {S T : Finset α}
    (hA : DependsOn A (↑S)) (hB : DependsOn B (↑T)) (hST : Disjoint S T) :
    poc_SlabCard A B :=
  (poc_perOrbitCard_iff_slabCard A B).mp (perOrbitCard_of_disjoint_support hA hB hST)


theorem poc_slabCard_of_box_empty {A B : Set (ConfigSpace α)}
    (hbox : disjointOccurrence A B = ∅) : poc_SlabCard A B :=
  (poc_perOrbitCard_iff_slabCard A B).mp (perOrbitCard_of_box_empty hbox)


theorem poc_slabCard_rbi : poc_SlabCard rbi_A rbi_B :=
  (poc_perOrbitCard_iff_slabCard rbi_A rbi_B).mp perOrbitCard_rbi


theorem poc_reimerCardForm_rbi : poc_ReimerCardForm rbi_A rbi_B :=
  poc_reimerCardForm_of_slabCard rbi_A rbi_B poc_slabCard_rbi


theorem reimer_wprob_of_slabCard (φ : α → Bool → ℝ) (hφ0 : ∀ x b, 0 ≤ φ x b)
    (hφ1 : ∀ x, φ x false + φ x true = 1) {A B : Set (ConfigSpace α)}
    (h : poc_SlabCard A B) :
    wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B :=
  reimer_wprob_of_perOrbitCard φ hφ0 hφ1 ((poc_perOrbitCard_iff_slabCard A B).mpr h)


end StatMech

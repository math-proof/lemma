/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPerScaleBijClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexW2Weight.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexSurgerySeams.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexPerScaleBijClose.Part4


namespace StatMech.Universality

open scoped BigOperators

open Filter Topology


theorem hpb_emptyD_summable (a : ℂ) (h0 : ℤ) (x : ℝ) :
    Summable (fun d : {ts // (fun _ : List ℤ => False) ts} => hexSAWwt a h0 x d.1) := by
  have : IsEmpty {ts : List ℤ // (fun _ : List ℤ => False) ts} := ⟨fun d => d.2⟩
  exact summable_empty


theorem hpb_eD_empty_fires (a : ℂ) (h0 : ℤ) (x : ℝ) (P : List ℤ → Prop)
    (hsumP : Summable (fun n : {ts // P ts} => hexSAWwt a h0 x n.1)) :
    (∑' d : {ts // P ts ∧ ¬ P ts}, hexSAWwt a h0 x d.1)
      = hpb_lamS a h0 x P - hpb_lamS a h0 x P := by
  unfold hpb_lamS
  exact hpb_tsum_setDiff P P (hexSAWwt a h0 x) (fun _ h => h) hsumP


theorem hpb_eB_empty_fires (a : ℂ) (h0 : ℤ) (memB : List ℤ → Prop)
    (hBsum : Summable (fun b : {ts // memB ts} => hexSAWwt a h0 hexChiE b.1)) :
    (∑' b, (hpb_cut a h0 (fun _ => False) memB
        (hpb_emptyHalfClass a h0 hexChiE memB) (hpb_emptyD_summable a h0 hexChiE) hBsum).wtB b)
      = hpb_upsS a h0 hexChiE memB :=
  hpb_cut_wtB_sum a h0 (fun _ => False) memB
    (hpb_emptyHalfClass a h0 hexChiE memB) (hpb_emptyD_summable a h0 hexChiE) hBsum


theorem hpb_data_satisfiable :
    ∃ (a0 : ℂ) (h0 : ℤ) (memA memB : ℕ → List ℤ → Prop),
      (∀ v ts, memA v ts → memA (v + 1) ts) ∧
      (∀ v, Nonempty (HexHalfClass a0 h0 hexChiE
        (fun ts => memA (v + 1) ts ∧ ¬ memA v ts) (memB (v + 1)))) ∧
      (∀ v, Summable (fun d : {ts // memA (v + 1) ts ∧ ¬ memA v ts} =>
        hexSAWwt a0 h0 hexChiE d.1)) ∧
      (∀ v, Summable (fun b : {ts // memB (v + 1) ts} => hexSAWwt a0 h0 hexChiE b.1)) := by
  refine ⟨0, 0, (fun _ _ => False), (fun _ ts => ts = []), ?_, ?_, ?_, ?_⟩
  · intro _ _ h; exact h
  · intro v
    have heq : (fun ts => (fun _ : List ℤ => False) ts ∧ ¬ (fun _ : List ℤ => False) ts)
        = (fun _ : List ℤ => False) := by funext ts; simp
    rw [heq]; exact ⟨hpb_emptyHalfClass 0 0 hexChiE (fun ts => ts = [])⟩
  · intro v
    have heq : (fun ts => (fun _ : List ℤ => False) ts ∧ ¬ (fun _ : List ℤ => False) ts)
        = (fun _ : List ℤ => False) := by funext ts; simp
    rw [heq]; exact hpb_emptyD_summable 0 0 hexChiE
  · intro v
    haveI : Subsingleton {ts : List ℤ // ts = []} :=
      ⟨fun a b => Subtype.ext (a.2.trans b.2.symm)⟩
    haveI : Finite {ts : List ℤ // ts = []} := Finite.of_subsingleton
    exact Summable.of_finite

end StatMech.Universality

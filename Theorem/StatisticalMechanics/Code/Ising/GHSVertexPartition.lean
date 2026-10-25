/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Inequalities.FKG
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Walls.ghysupermult.Part2
open Finset Classical

set_option maxHeartbeats 1600000


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls

variable {W : Type*} [Fintype W] [DecidableEq W]


lemma ghsvp_wJ_zero_factor (E : Finset (Sym2 W)) (J : Sym2 W -> Real)
    (s : ConfigSpace W) :
    wJ E J (fun _ => 0) s =
      ∏ e ∈ E, (Real.cosh (J e) + bond s e * Real.sinh (J e)) := by
  unfold wJ
  simp only [zero_mul, Finset.sum_const_zero, add_zero]
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro e _
  exact exp_mul_pm (J e) (bond s e) (bond_eq_pm s e)


lemma ghsvp_wJ_factor (E : Finset (Sym2 W)) (J : Sym2 W -> Real)
    (hf : W -> Real) (s : ConfigSpace W) :
    wJ E J hf s =
      (∏ e ∈ E, (Real.cosh (J e) + bond s e * Real.sinh (J e))) *
        ∏ x : W, (Real.cosh (hf x) + spin s x * Real.sinh (hf x)) := by
  unfold wJ
  rw [Real.exp_add, Real.exp_sum, Real.exp_sum]
  congr 1
  · apply Finset.prod_congr rfl
    intro e _
    exact exp_mul_pm (J e) (bond s e) (bond_eq_pm s e)
  · apply Finset.prod_congr rfl
    intro x _
    exact exp_mul_pm (hf x) (spin s x) (spin_eq_pm s x)


lemma ghsvp_expJ_nonneg (E : Finset (Sym2 W)) (J : Sym2 W -> Real)
    (hf : W -> Real) (hJ : ∀ e ∈ E, 0 <= J e) (hhf : ∀ x, 0 <= hf x)
    (A : Finset W) : 0 <= expJ E J hf (spinProd A) := by
  unfold expJ
  apply div_nonneg
  · rw [show (∑ s : ConfigSpace W, spinProd A s * wJ E J hf s) =
        ∑ s : ConfigSpace W, spinProd A s *
          ((∏ e ∈ E, (Real.cosh (J e) + bond s e * Real.sinh (J e))) *
            ∏ x : W, (Real.cosh (hf x) + spin s x * Real.sinh (hf x))) by
      apply Finset.sum_congr rfl
      intro s _
      rw [ghsvp_wJ_factor]]
    exact inner_sum_nonneg' E
      (fun e => Real.cosh (J e)) (fun e => Real.sinh (J e))
      (fun x => Real.cosh (hf x)) (fun x => Real.sinh (hf x))
      (fun e _ => (Real.cosh_pos _).le)
      (fun e he => Real.sinh_nonneg_iff.mpr (hJ e he))
      (fun x => (Real.cosh_pos _).le)
      (fun x => Real.sinh_nonneg_iff.mpr (hhf x))
      (spinProd A) (isSpinMonomial_spinProd A)
  · exact (ZJ_pos E J hf).le


lemma ghsvp_expJ_zero_nonneg (E : Finset (Sym2 W)) (J : Sym2 W -> Real)
    (hJ : ∀ e ∈ E, 0 <= J e) (A : Finset W) :
    0 <= expJ E J (fun _ => 0) (spinProd A) := by
  unfold expJ
  apply div_nonneg
  · rw [show (∑ s : ConfigSpace W, spinProd A s * wJ E J (fun _ => 0) s) =
        ∑ s : ConfigSpace W, spinProd A s *
          ∏ e ∈ E, (Real.cosh (J e) + Real.sinh (J e) * bond s e) by
      apply Finset.sum_congr rfl
      intro s _
      rw [ghsvp_wJ_zero_factor]
      congr 1
      apply Finset.prod_congr rfl
      intro e _
      ring]
    simpa [mul_comm] using inner_sum_nonneg' E
      (fun e => Real.cosh (J e)) (fun e => Real.sinh (J e))
      (fun _ => 1) (fun _ => 0)
      (fun e _ => (Real.cosh_pos _).le)
      (fun e he => Real.sinh_nonneg_iff.mpr (hJ e he))
      (fun _ => by norm_num) (fun _ => by norm_num)
      (spinProd A) (isSpinMonomial_spinProd A)
  · exact (ZJ_pos E J (fun _ => 0)).le


lemma ghsvp_ZJ_zero_mono (J : Sym2 W -> Real) (hJ : forall e, 0 <= J e)
    (E F : Finset (Sym2 W)) (hEF : E ⊆ F) (hnd : ∀ e ∈ F, ¬ e.IsDiag) :
    ZJ E J (fun _ => 0) <= ZJ F J (fun _ => 0) := by
  have hadd : ∀ D : Finset (Sym2 W), Disjoint D E → (∀ e ∈ D, ¬ e.IsDiag) →
      ZJ E J (fun _ => 0) <= ZJ (D ∪ E) J (fun _ => 0) := by
    intro D
    induction D using Finset.induction with
    | empty => simp
    | @insert e D he ih =>
        intro hdisj hdiag
        have hdisjD : Disjoint D E := hdisj.mono_left (Finset.subset_insert e D)
        have hdiagD : ∀ a ∈ D, ¬ a.IsDiag :=
          fun a ha => hdiag a (Finset.mem_insert_of_mem ha)
        have hi := ih hdisjD hdiagD
        have heE : e ∉ E := fun heE =>
          (Finset.disjoint_left.mp hdisj (Finset.mem_insert_self e D)) heE
        obtain ⟨x, y, hxy, rfl⟩ :=
          exists_pair_of_not_isDiag (hdiag e (Finset.mem_insert_self e D))
        have hedge : s(x, y) ∉ D ∪ E := by simp [he, heE]
        have hins := ghy_ZJ_insert_factor (D ∪ E) J (fun _ => 0) hxy hedge
        have hcorr : 0 <= expJ (D ∪ E) J (fun _ => 0) (spinProd {x, y}) :=
          ghsvp_expJ_zero_nonneg (D ∪ E) J (fun a _ => hJ a) {x, y}
        have hc : 1 <= Real.cosh (J s(x, y)) := Real.one_le_cosh _
        have hs : 0 <= Real.sinh (J s(x, y)) := Real.sinh_nonneg_iff.mpr (hJ _)
        have hstep : ZJ (D ∪ E) J (fun _ => 0) <=
            ZJ (insert s(x, y) (D ∪ E)) J (fun _ => 0) := by
          rw [hins]
          nlinarith [ZJ_pos (D ∪ E) J (fun _ => 0), mul_nonneg hs hcorr]
        rw [Finset.insert_union]
        exact hi.trans hstep
  have h := hadd (F \ E) Finset.sdiff_disjoint (by
    intro e he
    exact hnd e (Finset.mem_sdiff.mp he).1)
  rwa [Finset.sdiff_union_of_subset hEF] at h


lemma ghsvp_ZJ_zero_logSupermodular (J : Sym2 W -> Real) (hJ : forall e, 0 <= J e)
    (E F : Finset (Sym2 W)) (hnd : ∀ e ∈ E ∪ F, ¬ e.IsDiag) :
    ZJ E J (fun _ => 0) * ZJ F J (fun _ => 0) <=
      ZJ (E ∪ F) J (fun _ => 0) * ZJ (E ∩ F) J (fun _ => 0) := by
  have hsub : E ∩ F ⊆ E := Finset.inter_subset_left
  have hdisj : Disjoint (F \ E) E := Finset.sdiff_disjoint
  have hndE : ∀ e ∈ E, ¬ e.IsDiag := fun e he => hnd e (Finset.mem_union_left F he)
  have hndD : ∀ e ∈ F \ E, ¬ e.IsDiag := by
    intro e he
    exact hnd e (Finset.mem_union_right E (Finset.mem_sdiff.mp he).1)
  have h := ghy_ZJ_supermod J (fun _ => 0) hJ (fun _ => le_rfl)
    (E ∩ F) E hsub hndE (F \ E) hdisj hndD
  have hleft : (E ∩ F) ∪ (F \ E) = F := by
    ext e
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hright : E ∪ (F \ E) = E ∪ F := by
    ext e
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  rw [hleft, hright] at h
  nlinarith [h]


end StatMech.Ising

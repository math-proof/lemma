/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompression.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.BK.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part3
import Mathlib.Combinatorics.SetFamily.Compression.Down
import Def.StatisticalMechanics.Code.Inequalities.ReimerCompression.Part5
open MeasureTheory Finset
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {E : Type*}


lemma DependsOn.mono {A : Set (ConfigSpace E)} {S S' : Set E} (h : DependsOn A S)
    (hSS' : S ⊆ S') : DependsOn A S' :=
  fun ω ω' hag => h ω ω' (agreeOn_mono hSS' hag)


lemma DependsOn.occursOn_iff {A : Set (ConfigSpace E)} {S : Set E} (h : DependsOn A S)
    (ω : ConfigSpace E) : OccursOn A S ω ↔ ω ∈ A :=
  ⟨OccursOn.mem_self, fun hω ω' hω' => (h ω ω' hω').mp hω⟩


theorem disjointOccurrence_eq_inter_of_dependsOn {A B : Set (ConfigSpace E)} {S T : Set E}
    (hA : DependsOn A S) (hB : DependsOn B T) (hST : Disjoint S T) :
    disjointOccurrence A B = A ∩ B := by
  apply Set.Subset.antisymm (disjointOccurrence_subset_inter A B)
  rintro ω ⟨hAω, hBω⟩
  exact ⟨S, T, hST, (hA.occursOn_iff ω).mpr hAω, (hB.occursOn_iff ω).mpr hBω⟩


lemma pweight_split [Fintype E] (P : E → Prop) [DecidablePred P] (φ : E → Bool → ℝ)
    (a : {x // P x} → Bool) (b : {x // ¬ P x} → Bool) :
    pweight φ ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (a, b))
      = (∏ i : {x // P x}, φ i (a i)) * (∏ i : {x // ¬ P x}, φ i (b i)) := by
  simp only [pweight]
  rw [← Fintype.prod_subtype_mul_prod_subtype P
        (fun i => φ i ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (a, b) i))]
  congr 1
  · exact Finset.prod_congr rfl
      (fun i _ => by rw [Equiv.piEquivPiSubtypeProd_symm_apply, dif_pos i.2])
  · exact Finset.prod_congr rfl
      (fun i _ => by rw [Equiv.piEquivPiSubtypeProd_symm_apply, dif_neg i.2])


lemma wprob_reindex [Fintype E] [DecidableEq E] (P : E → Prop) [DecidablePred P]
    (φ : E → Bool → ℝ) (S : Set (ConfigSpace E)) :
    wprob φ S = ∑ a : {x // P x} → Bool, ∑ b : {x // ¬ P x} → Bool,
      S.indicator (fun _ => (1 : ℝ)) ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (a, b))
        * pweight φ ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (a, b)) := by
  simp only [wprob]
  rw [← (Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm.sum_comp
    (fun ω => S.indicator (fun _ => (1 : ℝ)) ω * pweight φ ω)]
  rw [Fintype.sum_prod_type]


lemma indicator_indep_compl {A : Set (ConfigSpace E)} (P : E → Prop) [DecidablePred P]
    (hA : DependsOn A {x | P x}) (a : {x // P x} → Bool) (b b' : {x // ¬ P x} → Bool) :
    A.indicator (fun _ => (1 : ℝ)) ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (a, b))
      = A.indicator (fun _ => (1 : ℝ))
          ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (a, b')) := by
  have hag : agreeOn {x | P x}
      ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (a, b))
      ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (a, b')) := by
    intro e he; simp only [Set.mem_setOf_eq] at he
    rw [Equiv.piEquivPiSubtypeProd_symm_apply, Equiv.piEquivPiSubtypeProd_symm_apply,
      dif_pos he, dif_pos he]
  have := hA _ _ hag
  by_cases h : ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (a, b)) ∈ A
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (this.mp h)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun hc => h (this.mpr hc))]


lemma indicator_indep_pred {B : Set (ConfigSpace E)} (P : E → Prop) [DecidablePred P]
    (hB : DependsOn B {x | ¬ P x}) (a a' : {x // P x} → Bool) (b : {x // ¬ P x} → Bool) :
    B.indicator (fun _ => (1 : ℝ)) ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (a, b))
      = B.indicator (fun _ => (1 : ℝ))
          ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (a', b)) := by
  have hag : agreeOn {x | ¬ P x}
      ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (a, b))
      ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (a', b)) := by
    intro e he; simp only [Set.mem_setOf_eq] at he
    rw [Equiv.piEquivPiSubtypeProd_symm_apply, Equiv.piEquivPiSubtypeProd_symm_apply,
      dif_neg he, dif_neg he]
  have := hB _ _ hag
  by_cases h : ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (a, b)) ∈ B
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (this.mp h)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun hc => h (this.mpr hc))]


lemma sum_prod_eq_one {S : Type*} [Fintype S] [DecidableEq S] (ψ : S → Bool → ℝ)
    (h : ∀ s, ψ s false + ψ s true = 1) :
    (∑ a : S → Bool, ∏ s, ψ s (a s)) = 1 := by
  rw [← Fintype.prod_sum (fun s => ψ s)]; simp only [Fintype.sum_bool]
  exact Finset.prod_eq_one (fun s _ => by rw [add_comm]; exact h s)

set_option maxHeartbeats 1000000 in


theorem wprob_inter_mul_of_split [Fintype E] [DecidableEq E] (P : E → Prop) [DecidablePred P]
    (φ : E → Bool → ℝ) (hφ1 : ∀ x, φ x false + φ x true = 1)
    {A B : Set (ConfigSpace E)} (hA : DependsOn A {x | P x}) (hB : DependsOn B {x | ¬ P x}) :
    wprob φ (A ∩ B) = wprob φ A * wprob φ B := by
  classical
  set e := Equiv.piEquivPiSubtypeProd P (fun _ : E => Bool) with he
  set IA : ({x // P x} → Bool) → ({x // ¬ P x} → Bool) → ℝ :=
    fun a b => A.indicator (fun _ => (1 : ℝ)) (e.symm (a, b)) with hIA
  set IB : ({x // P x} → Bool) → ({x // ¬ P x} → Bool) → ℝ :=
    fun a b => B.indicator (fun _ => (1 : ℝ)) (e.symm (a, b)) with hIB
  set WP : ({x // P x} → Bool) → ℝ := fun a => ∏ i : {x // P x}, φ i (a i) with hWP
  set WQ : ({x // ¬ P x} → Bool) → ℝ := fun b => ∏ i : {x // ¬ P x}, φ i (b i) with hWQ
  let b0 : {x // ¬ P x} → Bool := fun _ => false
  let a0 : {x // P x} → Bool := fun _ => false
  have hIAb : ∀ a b, IA a b = IA a b0 := fun a b => indicator_indep_compl P hA a b b0
  have hIBa : ∀ a b, IB a b = IB a0 b := fun a b => indicator_indep_pred P hB a a0 b
  have hsumWQ : (∑ b : {x // ¬ P x} → Bool, WQ b) = 1 :=
    sum_prod_eq_one (S := {x // ¬ P x}) (fun i b => φ (i : E) b) (fun i => hφ1 (i : E))
  have hsumWP : (∑ a : {x // P x} → Bool, WP a) = 1 :=
    sum_prod_eq_one (S := {x // P x}) (fun i b => φ (i : E) b) (fun i => hφ1 (i : E))
  have hABind : ∀ a b, (A ∩ B).indicator (fun _ => (1 : ℝ)) (e.symm (a, b)) = IA a b * IB a b := by
    intro a b
    by_cases hAm : e.symm (a, b) ∈ A <;> by_cases hBm : e.symm (a, b) ∈ B <;>
      simp [hIA, hIB, Set.indicator, Set.mem_inter_iff, hAm, hBm]
  have hwAB : wprob φ (A ∩ B) = (∑ a, IA a b0 * WP a) * (∑ b, IB a0 b * WQ b) := by
    rw [wprob_reindex P φ (A ∩ B), Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    rw [hABind a b, pweight_split, hIAb a b, hIBa a b]; ring
  have hwA : wprob φ A = ∑ a, IA a b0 * WP a := by
    rw [wprob_reindex P φ A]
    apply Finset.sum_congr rfl; intro a _
    calc (∑ b : {x // ¬ P x} → Bool,
            A.indicator (fun _ => (1 : ℝ)) (e.symm (a, b)) * pweight φ (e.symm (a, b)))
        = ∑ b : {x // ¬ P x} → Bool, IA a b0 * WP a * WQ b := by
          apply Finset.sum_congr rfl; intro b _
          rw [pweight_split,
            show A.indicator (fun _ => (1 : ℝ)) (e.symm (a, b)) = IA a b from rfl, hIAb a b]; ring
      _ = IA a b0 * WP a := by rw [← Finset.mul_sum, hsumWQ, mul_one]
  have hwB : wprob φ B = ∑ b, IB a0 b * WQ b := by
    rw [wprob_reindex P φ B, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro b _
    calc (∑ a : {x // P x} → Bool,
            B.indicator (fun _ => (1 : ℝ)) (e.symm (a, b)) * pweight φ (e.symm (a, b)))
        = ∑ a : {x // P x} → Bool, IB a0 b * WQ b * WP a := by
          apply Finset.sum_congr rfl; intro a _
          rw [pweight_split,
            show B.indicator (fun _ => (1 : ℝ)) (e.symm (a, b)) = IB a b from rfl, hIBa a b]; ring
      _ = IB a0 b * WQ b := by rw [← Finset.mul_sum, hsumWP, mul_one]
  rw [hwAB, hwA, hwB]


theorem reimer_wprob_of_disjoint_support [Fintype E] [DecidableEq E] (φ : E → Bool → ℝ)
    (hφ1 : ∀ x, φ x false + φ x true = 1)
    {A B : Set (ConfigSpace E)} {S T : Set E}
    (hA : DependsOn A S) (hB : DependsOn B T) (hST : Disjoint S T) :
    wprob φ (disjointOccurrence A B) = wprob φ A * wprob φ B := by
  classical
  have hAP : DependsOn A {x | x ∈ S} := hA
  have hTcompl : T ⊆ {x | x ∉ S} := by
    intro x hx; simp only [Set.mem_setOf_eq]
    exact fun hxS => (Set.disjoint_left.mp hST) hxS hx
  have hBP : DependsOn B {x | ¬ (x ∈ S)} := hB.mono hTcompl
  rw [disjointOccurrence_eq_inter_of_dependsOn hA hB hST]
  exact wprob_inter_mul_of_split (fun x => x ∈ S) φ hφ1 hAP hBP


end StatMech

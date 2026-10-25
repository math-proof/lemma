/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CurrentRep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000


namespace StatMech

namespace Sharpness

open StatMech.Ising


theorem prod_tsum_fubini {ι : Type*} [DecidableEq ι] (g : ι → ℕ → ℝ)
    (hg : ∀ i, Summable (g i)) (hgnn : ∀ i k, 0 ≤ g i k) (s : Finset ι) :
    Summable (fun m : ↥s → ℕ => ∏ i : ↥s, g i.1 (m i)) ∧
    (∏ i ∈ s, ∑' k : ℕ, g i k)
      = ∑' (m : ↥s → ℕ), ∏ i : ↥s, g i.1 (m i) := by
  classical
  induction s using Finset.induction with
  | empty =>
    refine ⟨summable_of_hasFiniteSupport (Set.toFinite _), ?_⟩
    simp only [Finset.prod_empty]
    rw [tsum_eq_single (default : (↥(∅ : Finset ι) → ℕ))]
    · simp
    · intro m hm; exact absurd (Subsingleton.elim m _) hm
  | @insert a s ha IH =>
    obtain ⟨IHsum, IHeq⟩ := IH
    
    have prodsplit : ∀ m : ↥(insert a s) → ℕ,
        (∏ i : ↥(insert a s), g i.1 (m i))
          = g a (m ⟨a, Finset.mem_insert_self a s⟩) *
            ∏ i : ↥s, g i.1 (m ⟨i.1, Finset.mem_insert_of_mem i.2⟩) := by
      intro m
      rw [← Equiv.prod_comp (Finset.subtypeInsertEquivOption ha).symm
            (fun i : ↥(insert a s) => g i.1 (m i)), Fintype.prod_option]; rfl
    
    set E : (↥(insert a s) → ℕ) ≃ ℕ × (↥s → ℕ) :=
      (Equiv.arrowCongr (Finset.subtypeInsertEquivOption ha) (Equiv.refl ℕ)).trans
        Equiv.piOptionEquivProd with hE
    
    have hcomp : ∀ p : ℕ × (↥s → ℕ),
        (fun m : ↥(insert a s) → ℕ => ∏ i : ↥(insert a s), g i.1 (m i)) (E.symm p)
          = g a p.1 * ∏ i : ↥s, g i.1 (p.2 i) := by
      rintro ⟨k, ms⟩
      have happ : ∀ i : ↥(insert a s),
          E.symm (k, ms) i = (Finset.subtypeInsertEquivOption ha i).elim k ms := by
        intro i
        simp only [E, Equiv.symm_trans_apply, Function.comp_apply, Equiv.arrowCongr_symm,
          Equiv.arrowCongr_apply, Equiv.symm_symm, Equiv.refl_symm, Equiv.coe_refl, id_eq,
          Equiv.piOptionEquivProd_symm_apply]
        cases (Finset.subtypeInsertEquivOption ha i) <;> rfl
      simp only
      rw [show (∏ i : ↥(insert a s), g i.1 (E.symm (k, ms) i))
            = ∏ i : ↥(insert a s), g i.1 ((Finset.subtypeInsertEquivOption ha i).elim k ms) from
          Finset.prod_congr rfl (fun i _ => by rw [happ])]
      rw [← Equiv.prod_comp (Finset.subtypeInsertEquivOption ha).symm
            (fun i : ↥(insert a s) => g i.1 ((Finset.subtypeInsertEquivOption ha i).elim k ms)),
        Fintype.prod_option]
      simp only [Equiv.apply_symm_apply, Option.elim]
      have hnone : ((Finset.subtypeInsertEquivOption ha).symm none).1 = a := rfl
      have hsome : ∀ z : ↥s, ((Finset.subtypeInsertEquivOption ha).symm (some z)).1 = z.1 :=
        fun _ => rfl
      rw [hnone]
      exact congrArg _ (Finset.prod_congr rfl (fun z _ => by rw [hsome]))
    
    clear_value E
    clear hE
    have hjoint : Summable (fun p : ℕ × (↥s → ℕ) => g a p.1 * ∏ i : ↥s, g i.1 (p.2 i)) := by
      apply Summable.mul_of_nonneg (hg a) IHsum
      · intro k; exact hgnn a k
      · intro ms; exact Finset.prod_nonneg (fun i _ => hgnn i.1 _)
    refine ⟨?_, ?_⟩
    · rw [← E.symm.summable_iff]
      have : (fun m => ∏ i : ↥(insert a s), g i.1 (m i)) ∘ E.symm
          = fun p : ℕ × (↥s → ℕ) => g a p.1 * ∏ i : ↥s, g i.1 (p.2 i) := funext hcomp
      rw [this]; exact hjoint
    · rw [Finset.prod_insert ha, IHeq, Summable.tsum_mul_tsum (hg a) IHsum hjoint]
      have hreindex :
          (∑' (m : ↥(insert a s) → ℕ), ∏ i : ↥(insert a s), g i.1 (m i))
            = ∑' (p : ℕ × (↥s → ℕ)), g a p.1 * ∏ i : ↥s, g i.1 (p.2 i) :=
        (E.symm.tsum_eq (fun m => ∏ i : ↥(insert a s), g i.1 (m i))).symm.trans
          (tsum_congr hcomp)
      rw [hreindex]


theorem summable_prod_signed {ι : Type*} [DecidableEq ι] (g : ι → ℕ → ℝ)
    (hgn : ∀ i, Summable (fun k => ‖g i k‖)) (s : Finset ι) :
    Summable (fun m : ↥s → ℕ => ∏ i : ↥s, g i.1 (m i)) := by
  apply Summable.of_norm
  apply ((prod_tsum_fubini (fun i k => ‖g i k‖) hgn (fun i k => norm_nonneg _) s).1).congr
  intro m; rw [norm_prod]


theorem signed_prod_tsum_fubini {ι : Type*} [DecidableEq ι] (g : ι → ℕ → ℝ)
    (hg : ∀ i, Summable (g i)) (hgn : ∀ i, Summable (fun k => ‖g i k‖)) (s : Finset ι) :
    (∏ i ∈ s, ∑' k : ℕ, g i k) = ∑' (m : ↥s → ℕ), ∏ i : ↥s, g i.1 (m i) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty]
    rw [tsum_eq_single (default : (↥(∅ : Finset ι) → ℕ))]
    · simp
    · intro m hm; exact absurd (Subsingleton.elim m _) hm
  | @insert a s ha IH =>
    have IHsum : Summable (fun m : ↥s → ℕ => ∏ i : ↥s, g i.1 (m i)) :=
      summable_prod_signed g hgn s
    have prodsplit : ∀ m : ↥(insert a s) → ℕ,
        (∏ i : ↥(insert a s), g i.1 (m i))
          = g a (m ⟨a, Finset.mem_insert_self a s⟩) *
            ∏ i : ↥s, g i.1 (m ⟨i.1, Finset.mem_insert_of_mem i.2⟩) := by
      intro m
      rw [← Equiv.prod_comp (Finset.subtypeInsertEquivOption ha).symm
            (fun i : ↥(insert a s) => g i.1 (m i)), Fintype.prod_option]; rfl
    set E : (↥(insert a s) → ℕ) ≃ ℕ × (↥s → ℕ) :=
      (Equiv.arrowCongr (Finset.subtypeInsertEquivOption ha) (Equiv.refl ℕ)).trans
        Equiv.piOptionEquivProd with hE
    have hcomp : ∀ p : ℕ × (↥s → ℕ),
        (fun m : ↥(insert a s) → ℕ => ∏ i : ↥(insert a s), g i.1 (m i)) (E.symm p)
          = g a p.1 * ∏ i : ↥s, g i.1 (p.2 i) := by
      rintro ⟨k, ms⟩
      have happ : ∀ i : ↥(insert a s),
          E.symm (k, ms) i = (Finset.subtypeInsertEquivOption ha i).elim k ms := by
        intro i
        simp only [E, Equiv.symm_trans_apply, Function.comp_apply, Equiv.arrowCongr_symm,
          Equiv.arrowCongr_apply, Equiv.symm_symm, Equiv.refl_symm, Equiv.coe_refl, id_eq,
          Equiv.piOptionEquivProd_symm_apply]
        cases (Finset.subtypeInsertEquivOption ha i) <;> rfl
      simp only
      rw [show (∏ i : ↥(insert a s), g i.1 (E.symm (k, ms) i))
            = ∏ i : ↥(insert a s), g i.1 ((Finset.subtypeInsertEquivOption ha i).elim k ms) from
          Finset.prod_congr rfl (fun i _ => by rw [happ])]
      rw [← Equiv.prod_comp (Finset.subtypeInsertEquivOption ha).symm
            (fun i : ↥(insert a s) => g i.1 ((Finset.subtypeInsertEquivOption ha i).elim k ms)),
        Fintype.prod_option]
      simp only [Equiv.apply_symm_apply, Option.elim]
      have hnone : ((Finset.subtypeInsertEquivOption ha).symm none).1 = a := rfl
      have hsome : ∀ z : ↥s, ((Finset.subtypeInsertEquivOption ha).symm (some z)).1 = z.1 :=
        fun _ => rfl
      rw [hnone]
      exact congrArg _ (Finset.prod_congr rfl (fun z _ => by rw [hsome]))
    clear_value E
    clear hE
    
    
    have hjoint : Summable (fun p : ℕ × (↥s → ℕ) => g a p.1 * ∏ i : ↥s, g i.1 (p.2 i)) := by
      have hbase : Summable (fun m : ↥(insert a s) → ℕ => ∏ i : ↥(insert a s), g i.1 (m i)) :=
        summable_prod_signed g hgn (insert a s)
      have := (E.symm.summable_iff
        (f := fun m : ↥(insert a s) → ℕ => ∏ i : ↥(insert a s), g i.1 (m i))).mpr hbase
      refine this.congr (fun p => ?_)
      exact hcomp p
    rw [Finset.prod_insert ha, IH, Summable.tsum_mul_tsum (hg a) IHsum hjoint]
    have hreindex :
        (∑' (m : ↥(insert a s) → ℕ), ∏ i : ↥(insert a s), g i.1 (m i))
          = ∑' (p : ℕ × (↥s → ℕ)), g a p.1 * ∏ i : ↥s, g i.1 (p.2 i) :=
      (E.symm.tsum_eq (fun m => ∏ i : ↥(insert a s), g i.1 (m i))).symm.trans
        (tsum_congr hcomp)
    rw [hreindex]


variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem sum_spinB_pow (m : ℕ) :
    (∑ b : Bool, (spinB b) ^ m) = if Even m then 2 else 0 := by
  rw [Fintype.sum_bool]
  show (1 : ℝ) ^ m + (-1) ^ m = _
  by_cases hm : Even m
  · rw [if_pos hm, hm.neg_one_pow]; norm_num
  · rw [if_neg hm, Nat.not_even_iff_odd] at *
    rw [hm.neg_one_pow]; norm_num


theorem bond_pow_eq_prod_filter (s : ConfigSpace V) (e : Sym2 V)
    (he : e ∈ G.edgeFinset) (k : ℕ) :
    (bond s e) ^ k = ∏ v ∈ univ.filter (fun v => v ∈ e), (spin s v) ^ k := by
  induction e with
  | h x y =>
    have hadj : G.Adj x y := by
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he; exact he
    have hxy : x ≠ y := G.ne_of_adj hadj
    rw [bond_mk, mul_pow]
    have hfil : univ.filter (fun v => v ∈ (s(x, y) : Sym2 V)) = {x, y} := by
      ext v; simp [Sym2.mem_iff]
    rw [hfil, Finset.prod_pair hxy]


theorem prod_bond_pow_eq_prod_spin_pow (n : Current V) (s : ConfigSpace V) :
    (∏ e ∈ G.edgeFinset, (bond s e) ^ (n e))
      = ∏ v : V, (spin s v) ^ (incidentFlux G n v) := by
  have hL : (∏ e ∈ G.edgeFinset, (bond s e) ^ (n e))
      = ∏ e ∈ G.edgeFinset, ∏ v ∈ univ.filter (fun v => v ∈ e), (spin s v) ^ (n e) :=
    Finset.prod_congr rfl (fun e he => bond_pow_eq_prod_filter G s e he (n e))
  have hR : (∏ v : V, (spin s v) ^ (incidentFlux G n v))
      = ∏ v : V, ∏ e ∈ G.edgeFinset.filter (fun e => v ∈ e), (spin s v) ^ (n e) := by
    refine Finset.prod_congr rfl (fun v _ => ?_)
    unfold incidentFlux
    rw [Finset.prod_pow_eq_pow_sum]
  rw [hL, hR]
  refine Finset.prod_comm' (s := G.edgeFinset)
    (t := fun e => univ.filter (fun v => v ∈ e))
    (s' := fun v => G.edgeFinset.filter (fun e => v ∈ e)) (t' := univ) ?_
  intro e v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  tauto


theorem sum_prod_spin_pow (e : V → ℕ) :
    (∑ s : ConfigSpace V, ∏ v : V, (spin s v) ^ (e v))
      = ∏ v : V, ∑ b : Bool, (spinB b) ^ (e v) := by
  simp_rw [spin_eq_spinB]
  exact (Fintype.prod_sum (fun (v : V) (b : Bool) => (spinB b) ^ (e v))).symm


theorem spinProd_eq_prod_pow (A : Finset V) (s : ConfigSpace V) :
    spinProd A s = ∏ v : V, (spin s v) ^ (if v ∈ A then 1 else 0) := by
  unfold spinProd
  rw [← Finset.prod_filter_mul_prod_filter_not univ (· ∈ A)
      (fun v => (spin s v) ^ (if v ∈ A then 1 else 0))]
  have h1 : (∏ v ∈ univ.filter (· ∈ A), (spin s v) ^ (if v ∈ A then 1 else 0))
      = ∏ v ∈ A, spin s v := by
    rw [Finset.filter_mem_eq_inter, univ_inter]
    exact Finset.prod_congr rfl (fun v hv => by rw [if_pos hv, pow_one])
  have h2 : (∏ v ∈ univ.filter (¬ · ∈ A), (spin s v) ^ (if v ∈ A then 1 else 0)) = 1 :=
    Finset.prod_eq_one (fun v hv => by
      rw [Finset.mem_filter] at hv; rw [if_neg hv.2, pow_zero])
  rw [h1, h2, mul_one]


theorem spinSum_monomial_eq (A : Finset V) (n : Current V) :
    (∑ s : ConfigSpace V, spinProd A s * ∏ e ∈ G.edgeFinset, (bond s e) ^ (n e))
      = if sources G n = A then (2 : ℝ) ^ (Fintype.card V) else 0 := by
  have hint : ∀ s : ConfigSpace V,
      spinProd A s * ∏ e ∈ G.edgeFinset, (bond s e) ^ (n e)
        = ∏ v : V, (spin s v) ^ (incidentFlux G n v + (if v ∈ A then 1 else 0)) := by
    intro s
    rw [spinProd_eq_prod_pow, prod_bond_pow_eq_prod_spin_pow, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun v _ => by rw [pow_add]; ring)
  simp_rw [hint]
  rw [sum_prod_spin_pow]
  simp_rw [sum_spinB_pow]
  by_cases hsrc : sources G n = A
  · rw [if_pos hsrc]
    rw [Finset.prod_congr rfl (g := fun _ => (2 : ℝ)) ?_]
    · rw [Finset.prod_const, Finset.card_univ]
    · intro v _
      rw [if_pos]
      rw [show (if v ∈ A then 1 else 0) = (if v ∈ sources G n then 1 else 0) by rw [hsrc]]
      simp only [mem_sources]
      by_cases hv : Odd (incidentFlux G n v)
      · rw [if_pos hv]; rcases hv with ⟨c, hc⟩; rw [hc]; exact ⟨c + 1, by ring⟩
      · rw [if_neg hv, add_zero]; rw [Nat.not_odd_iff_even] at hv; exact hv
  · rw [if_neg hsrc]
    have hex : ∃ v, ¬ (v ∈ sources G n ↔ v ∈ A) := by
      by_contra h
      push Not at h
      exact hsrc (Finset.ext (fun v => h v))
    obtain ⟨v, hv⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    rw [if_neg]
    rw [mem_sources] at hv
    by_cases hva : v ∈ A
    · rw [if_pos hva]
      simp only [hva, iff_true] at hv
      rw [Nat.not_odd_iff_even] at hv
      rw [Nat.not_even_iff_odd]; rcases hv with ⟨c, hc⟩; rw [hc]; exact ⟨c, by ring⟩
    · rw [if_neg hva, add_zero]
      simp only [hva, iff_false] at hv
      rw [not_not] at hv
      rw [Nat.not_even_iff_odd]; exact hv


end Sharpness
end StatMech

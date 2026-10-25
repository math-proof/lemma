/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve3.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyProve2.Part2
import Mathlib.Combinatorics.SetFamily.HarrisKleitman
import Def.StatisticalMechanics.Code.Inequalities.ReimerButterflyProve3
open Finset
open scoped FinsetFamily


namespace StatMech

variable {α : Type*} [DecidableEq α]


@[simp] theorem iterDownComp_nil (𝒜 : Finset (Finset α)) : iterDownComp [] 𝒜 = 𝒜 := rfl

@[simp] theorem iterDownComp_cons (i : α) (cs : List α) (𝒜 : Finset (Finset α)) :
    iterDownComp (i :: cs) 𝒜 = Down.compression i (iterDownComp cs 𝒜) := rfl


theorem iterDownComp_card (cs : List α) (𝒜 : Finset (Finset α)) :
    (iterDownComp cs 𝒜).card = 𝒜.card := by
  induction cs with
  | nil => rfl
  | cons i cs ih => rw [iterDownComp_cons, Down.card_compression, ih]


theorem dpairsCount_iterDownComp_mono (cs : List α) (𝒜 ℬ : Finset (Finset α)) :
    dpairsCount 𝒜 ℬ ≤ dpairsCount (iterDownComp cs 𝒜) (iterDownComp cs ℬ) := by
  induction cs with
  | nil => simp
  | cons i cs ih =>
      rw [iterDownComp_cons, iterDownComp_cons]
      exact le_trans ih (dpairsCount_downDown_mono _ _ i)

section Weighted

variable [Fintype α]


theorem wdpairs_iterDownComp_mono {w : α → Bool → ℝ} (hw : ∀ x b, 0 ≤ w x b) (cs : List α)
    (hdom : ∀ i ∈ cs, w i true ≤ w i false) (𝒜 ℬ : Finset (Finset α)) :
    wdpairs w 𝒜 ℬ ≤ wdpairs w (iterDownComp cs 𝒜) (iterDownComp cs ℬ) := by
  induction cs with
  | nil => simp
  | cons i cs ih =>
      rw [iterDownComp_cons, iterDownComp_cons]
      refine le_trans (ih (fun j hj => hdom j (List.mem_cons_of_mem i hj))) ?_
      exact wdpairs_downDown_mono hw i (hdom i (List.mem_cons_self)) _ _


theorem wdpairs_symm_iterDownComp_mono {w : α → Bool → ℝ} (hsym : ∀ x, w x false = w x true)
    (cs : List α) (𝒜 ℬ : Finset (Finset α)) :
    wdpairs w 𝒜 ℬ ≤ wdpairs w (iterDownComp cs 𝒜) (iterDownComp cs ℬ) := by
  induction cs with
  | nil => simp
  | cons i cs ih =>
      rw [iterDownComp_cons, iterDownComp_cons]
      exact le_trans ih (wdpairs_symm_downDown_mono hsym i _ _)

end Weighted


theorem dpairsCount_member_le_nonMember_of_isLowerSet {𝒜 ℬ : Finset (Finset α)}
    (h𝒜 : IsLowerSet (𝒜 : Set (Finset α))) (hℬ : IsLowerSet (ℬ : Set (Finset α))) (i : α) :
    dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i)
      ≤ dpairsCount (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i) :=
  le_trans
    (dpairsCount_mono_left _ h𝒜.memberSubfamily_subset_nonMemberSubfamily)
    (dpairsCount_mono_right _ hℬ.memberSubfamily_subset_nonMemberSubfamily)

section Weighted

variable [Fintype α]


theorem wdpairs'_member_le_nonMember_of_isLowerSet {w : α → Bool → ℝ} (hw : ∀ x b, 0 ≤ w x b)
    {𝒜 ℬ : Finset (Finset α)} (h𝒜 : IsLowerSet (𝒜 : Set (Finset α)))
    (hℬ : IsLowerSet (ℬ : Set (Finset α))) (i : α) :
    wdpairs' w i (𝒜.memberSubfamily i) (ℬ.memberSubfamily i)
      ≤ wdpairs' w i (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i) :=
  le_trans
    (wdpairs'_mono_left hw i _ h𝒜.memberSubfamily_subset_nonMemberSubfamily)
    (wdpairs'_mono_right hw i _ hℬ.memberSubfamily_subset_nonMemberSubfamily)


theorem fmarg'_mono {w : α → Bool → ℝ} (hw : ∀ x b, 0 ≤ w x b) (i : α)
    {𝒜 𝒜' : Finset (Finset α)} (h : 𝒜 ⊆ 𝒜') : fmarg' w i 𝒜 ≤ fmarg' w i 𝒜' := by
  unfold fmarg'
  exact Finset.sum_le_sum_of_subset_of_nonneg h (fun S _ _ => fwt'_nonneg hw i S)


theorem fmarg'_modular (w : α → Bool → ℝ) (i : α) (𝒜 ℬ : Finset (Finset α)) :
    fmarg' w i (𝒜 ∪ ℬ) + fmarg' w i (𝒜 ∩ ℬ) = fmarg' w i 𝒜 + fmarg' w i ℬ := by
  unfold fmarg'; exact Finset.sum_union_inter


theorem fmarg_le_downComp {w : α → Bool → ℝ} (hw : ∀ x b, 0 ≤ w x b) (i : α)
    (hdom : w i true ≤ w i false) (𝒜 : Finset (Finset α)) :
    fmarg w 𝒜 ≤ fmarg w (Down.compression i 𝒜) := by
  have hA := fmarg_split w 𝒜 i
  have hDA := fmarg_split w (Down.compression i 𝒜) i
  rw [downComp_memberSubfamily i 𝒜, downComp_nonMemberSubfamily i 𝒜] at hDA
  
  have hmod := fmarg'_modular w i (𝒜.memberSubfamily i) (𝒜.nonMemberSubfamily i)
  
  have hD : fmarg' w i (𝒜.nonMemberSubfamily i)
      ≤ fmarg' w i (𝒜.memberSubfamily i ∪ 𝒜.nonMemberSubfamily i) :=
    fmarg'_mono hw i Finset.subset_union_right
  have hw0 : 0 ≤ w i false := hw i false
  set w0 := w i false
  set w1 := w i true
  set Am := fmarg' w i (𝒜.memberSubfamily i)
  set An := fmarg' w i (𝒜.nonMemberSubfamily i)
  set DUc := fmarg' w i (𝒜.memberSubfamily i ∩ 𝒜.nonMemberSubfamily i)
  set Dcc := fmarg' w i (𝒜.memberSubfamily i ∪ 𝒜.nonMemberSubfamily i)
  
  have key : fmarg w (Down.compression i 𝒜) - fmarg w 𝒜 = (w0 - w1) * (Dcc - An) := by
    rw [hA, hDA]; linear_combination w1 * hmod
  nlinarith [key, mul_nonneg (sub_nonneg.mpr hdom) (sub_nonneg.mpr hD)]


theorem fmarg_le_iterDownComp {w : α → Bool → ℝ} (hw : ∀ x b, 0 ≤ w x b) (cs : List α)
    (hdom : ∀ i ∈ cs, w i true ≤ w i false) (𝒜 : Finset (Finset α)) :
    fmarg w 𝒜 ≤ fmarg w (iterDownComp cs 𝒜) := by
  induction cs with
  | nil => simp
  | cons i cs ih =>
      rw [iterDownComp_cons]
      refine le_trans (ih (fun j hj => hdom j (List.mem_cons_of_mem i hj))) ?_
      exact fmarg_le_downComp hw i (hdom i (List.mem_cons_self)) _

end Weighted


theorem iterDownComp_eq_self_of_isLowerSet {𝒜 : Finset (Finset α)}
    (h : IsLowerSet (𝒜 : Set (Finset α))) (cs : List α) :
    iterDownComp cs 𝒜 = 𝒜 := by
  induction cs with
  | nil => rfl
  | cons i cs ih =>
      rw [iterDownComp_cons, ih, downComp_eq_self_of_isLowerSet h i]


theorem downComp_eq_self_iff (i : α) (𝒜 : Finset (Finset α)) :
    Down.compression i 𝒜 = 𝒜 ↔ ∀ s ∈ 𝒜, s.erase i ∈ 𝒜 := by
  constructor
  · intro h s hs
    rw [← h] at hs ⊢
    exact Down.erase_mem_compression_of_mem_compression hs
  · intro h
    ext s
    rw [Down.mem_compression]
    constructor
    · rintro (⟨hs, _⟩ | ⟨_, hins⟩)
      · exact hs
      · have herase := h _ hins
        by_cases hi : i ∈ s
        · rwa [insert_eq_of_mem hi] at hins
        · rwa [erase_insert hi] at herase
    · intro hs
      exact Or.inl ⟨hs, h s hs⟩


theorem isLowerSet_of_erase_closed {𝒜 : Finset (Finset α)}
    (h : ∀ s ∈ 𝒜, ∀ i, s.erase i ∈ 𝒜) : IsLowerSet (𝒜 : Set (Finset α)) := by
  have key : ∀ (n : ℕ) (s t : Finset α), (s \ t).card = n → t ⊆ s → s ∈ 𝒜 → t ∈ 𝒜 := by
    intro n
    induction n with
    | zero =>
        intro s t hcard hts hs
        rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset] at hcard
        rwa [Finset.Subset.antisymm hcard hts] at hs
    | succ n ih =>
        intro s t hcard hts hs
        have hne : (s \ t).Nonempty := by rw [← Finset.card_pos, hcard]; omega
        obtain ⟨a, ha⟩ := hne
        rw [Finset.mem_sdiff] at ha
        have hsa : s.erase a ∈ 𝒜 := h s hs a
        have hts' : t ⊆ s.erase a := by
          intro x hx
          rw [Finset.mem_erase]
          exact ⟨fun hxa => ha.2 (hxa ▸ hx), hts hx⟩
        have hdiff : s.erase a \ t = (s \ t).erase a := by
          ext x; simp only [Finset.mem_sdiff, Finset.mem_erase]; tauto
        have hcard' : (s.erase a \ t).card = n := by
          rw [hdiff, Finset.card_erase_of_mem (by rw [Finset.mem_sdiff]; exact ha), hcard]
          omega
        exact ih (s.erase a) t hcard' hts' hsa
  intro s t hts hs
  rw [mem_coe] at hs ⊢
  exact key _ s t rfl hts hs


theorem isLowerSet_iff_forall_downComp_eq_self (𝒜 : Finset (Finset α)) :
    IsLowerSet (𝒜 : Set (Finset α)) ↔ ∀ i, Down.compression i 𝒜 = 𝒜 := by
  constructor
  · intro h i; exact downComp_eq_self_of_isLowerSet h i
  · intro h
    refine isLowerSet_of_erase_closed (fun s hs i => ?_)
    exact (downComp_eq_self_iff i 𝒜).1 (h i) s hs


theorem dpairsCount_le_endpoint (cs : List α) (𝒜 ℬ : Finset (Finset α))
    (h𝒜 : IsLowerSet ((iterDownComp cs 𝒜) : Set (Finset α)))
    (hℬ : IsLowerSet ((iterDownComp cs ℬ) : Set (Finset α))) :
    dpairsCount 𝒜 ℬ ≤ dpairsCount (iterDownComp cs 𝒜) (iterDownComp cs ℬ)
      ∧ (∀ i, Down.compression i (iterDownComp cs 𝒜) = iterDownComp cs 𝒜)
      ∧ (∀ i, Down.compression i (iterDownComp cs ℬ) = iterDownComp cs ℬ) :=
  ⟨dpairsCount_iterDownComp_mono cs 𝒜 ℬ,
   fun i => downComp_eq_self_of_isLowerSet h𝒜 i,
   fun i => downComp_eq_self_of_isLowerSet hℬ i⟩

section Weighted

variable [Fintype α]


theorem wdpairs_le_endpoint {w : α → Bool → ℝ} (hw : ∀ x b, 0 ≤ w x b) (cs : List α)
    (hdom : ∀ i ∈ cs, w i true ≤ w i false) (𝒜 ℬ : Finset (Finset α))
    (h𝒜 : IsLowerSet ((iterDownComp cs 𝒜) : Set (Finset α)))
    (hℬ : IsLowerSet ((iterDownComp cs ℬ) : Set (Finset α))) :
    wdpairs w 𝒜 ℬ ≤ wdpairs w (iterDownComp cs 𝒜) (iterDownComp cs ℬ)
      ∧ ∀ i, wdpairs' w i ((iterDownComp cs 𝒜).memberSubfamily i)
                ((iterDownComp cs ℬ).memberSubfamily i)
              ≤ wdpairs' w i ((iterDownComp cs 𝒜).nonMemberSubfamily i)
                  ((iterDownComp cs ℬ).nonMemberSubfamily i) :=
  ⟨wdpairs_iterDownComp_mono hw cs hdom 𝒜 ℬ,
   fun i => wdpairs'_member_le_nonMember_of_isLowerSet hw h𝒜 hℬ i⟩

end Weighted
end StatMech

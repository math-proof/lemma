/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Theorem.StatisticalMechanics.Code.Sharpness.ClaimIsing.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Def.StatisticalMechanics.Code.Sharpness.ClaimIsingFull.Part2
open SimpleGraph Finset
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000


namespace StatMech

namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem aFull_notIn (S : Finset V) (a) (i : ↥G.edgeFinset) (hi : ¬ isIn G S i) :
    aFull G S a i = 0 := by unfold aFull; rw [dif_neg hi]

theorem reEdge_apply (S : Finset V) (ab) (i : ↥G.edgeFinset) :
    reEdge G S ab i = if h : isIn G S i then ab.1 ⟨i, h⟩ else ab.2 ⟨i, h⟩ := by
  unfold reEdge; simp [Equiv.piEquivPiSubtypeProd]

theorem reEdge_zero_right (S : Finset V) (a) : reEdge G S (a, fun _ => 0) = aFull G S a := by
  funext i; rw [reEdge_apply]; unfold aFull; by_cases h : isIn G S i <;> simp [h]

theorem reEdge_eq_add (S : Finset V) (a b) (i : ↥G.edgeFinset) :
    reEdge G S (a, b) i = aFull G S a i + bFull G S b i := by
  rw [reEdge_apply]; unfold aFull bFull; by_cases h : isIn G S i <;> simp [h]


theorem ofEdgeFun_reEdge_add (S : Finset V) (a b) :
    (fun e => (ofEdgeFun G (aFull G S a)) e + (ofEdgeFun G (bFull G S b)) e)
      = ofEdgeFun G (reEdge G S (a, b)) := by
  funext e; unfold ofEdgeFun
  by_cases h : e ∈ G.edgeFinset
  · rw [dif_pos h, dif_pos h, dif_pos h, reEdge_eq_add]
  · rw [dif_neg h, dif_neg h, dif_neg h]


theorem aFull_bFull_disjoint (S : Finset V) (a b) (e : Sym2 V) :
    (ofEdgeFun G (aFull G S a)) e = 0 ∨ (ofEdgeFun G (bFull G S b)) e = 0 := by
  unfold ofEdgeFun
  by_cases h : e ∈ G.edgeFinset
  · rw [dif_pos h, dif_pos h]; unfold aFull bFull
    by_cases hi : isIn G S ⟨e, h⟩
    · right; rw [dif_pos hi]
    · left; rw [dif_neg hi]
  · left; rw [dif_neg h]


theorem weight_reEdge_split (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (a b) :
    weight G β J (ofEdgeFun G (reEdge G S (a, b)))
      = weight G β J (ofEdgeFun G (aFull G S a)) * weight G β J (ofEdgeFun G (bFull G S b)) := by
  rw [← ofEdgeFun_reEdge_add]
  unfold weight
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun e _ => ?_)
  have key : ∀ (x : ℝ) (p q : ℕ), p = 0 ∨ q = 0 →
      x ^ (p + q) / (Nat.factorial (p + q)) = x ^ p / (Nat.factorial p) * (x ^ q / (Nat.factorial q)) := by
    intro x p q hpq; rcases hpq with h | h <;> subst h <;> simp
  exact key (β * J e) _ _ (aFull_bFull_disjoint G S a b e)


theorem sources_reEdge_split (S : Finset V) (a b) :
    sources G (ofEdgeFun G (reEdge G S (a, b)))
      = sources G (ofEdgeFun G (aFull G S a)) ∆ sources G (ofEdgeFun G (bFull G S b)) := by
  rw [← ofEdgeFun_reEdge_add, sources_add]


theorem incidentFlux_aFull_zero (S : Finset V) (a) {v : V} (hv : v ∉ S) :
    incidentFlux G (ofEdgeFun G (aFull G S a)) v = 0 := by
  unfold incidentFlux
  apply Finset.sum_eq_zero
  intro e he
  rw [Finset.mem_filter] at he
  obtain ⟨hee, hve⟩ := he
  rw [SimpleGraph.mem_edgeFinset] at hee
  unfold ofEdgeFun aFull
  by_cases h : e ∈ G.edgeFinset
  · rw [dif_pos h]
    by_cases hi : isIn G S ⟨e, h⟩
    · exact absurd (hi v hve) hv
    · rw [dif_neg hi]
  · exact absurd (SimpleGraph.mem_edgeFinset.mpr hee) h


theorem sources_aFull_subset (S : Finset V) (a) :
    sources G (ofEdgeFun G (aFull G S a)) ⊆ S := by
  intro v hv
  rw [mem_sources] at hv
  by_contra hvS
  rw [incidentFlux_aFull_zero G S a hvS] at hv
  exact (Nat.not_odd_iff_even.mpr ⟨0, rfl⟩) hv


theorem incidentFlux_bFull_zero_of_noCross (S : Finset V) (b)
    (hcross : ∀ i : ↥G.edgeFinset, 1 ≤ bFull G S b i → edgeInside Sᶜ (i : Sym2 V))
    {v : V} (hv : v ∈ S) :
    incidentFlux G (ofEdgeFun G (bFull G S b)) v = 0 := by
  unfold incidentFlux
  apply Finset.sum_eq_zero
  intro e he
  rw [Finset.mem_filter] at he
  obtain ⟨hee, hve⟩ := he
  rw [SimpleGraph.mem_edgeFinset] at hee
  unfold ofEdgeFun
  by_cases h : e ∈ G.edgeFinset
  · rw [dif_pos h]
    by_cases hpos : 1 ≤ bFull G S b ⟨e, h⟩
    · have hvc := (hcross ⟨e, h⟩ hpos) v hve
      rw [Finset.mem_compl] at hvc; exact absurd hv hvc
    · omega
  · exact absurd (SimpleGraph.mem_edgeFinset.mpr hee) h


theorem sources_bFull_subset_compl (S : Finset V) (b)
    (hcross : ∀ i : ↥G.edgeFinset, 1 ≤ bFull G S b i → edgeInside Sᶜ (i : Sym2 V)) :
    sources G (ofEdgeFun G (bFull G S b)) ⊆ Sᶜ := by
  intro v hv
  rw [mem_sources] at hv
  rw [Finset.mem_compl]
  intro hvS
  rw [incidentFlux_bFull_zero_of_noCross G S b hcross hvS] at hv
  exact (Nat.not_odd_iff_even.mpr ⟨0, rfl⟩) hv


theorem weight_couplingIn_aFull (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (a) :
    weight G β (couplingIn J S) (ofEdgeFun G (aFull G S a))
      = weight G β J (ofEdgeFun G (aFull G S a)) := by
  rw [weight_ofEdgeFun, weight_ofEdgeFun]
  refine Finset.prod_congr rfl (fun e _ => ?_)
  unfold couplingIn
  by_cases hi : edgeInside S e.1
  · rw [if_pos hi]
  · rw [if_neg hi, aFull_notIn G S a e (by unfold isIn; exact hi)]; simp


theorem weight_reEdge_eq_zero (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (a)
    (b : {i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ)
    (j : {i : ↥G.edgeFinset // ¬ isIn G S i}) (hj : 1 ≤ b j) :
    weight G β (couplingIn J S) (ofEdgeFun G (reEdge G S (a, b))) = 0 := by
  rw [weight_ofEdgeFun]
  apply Finset.prod_eq_zero (Finset.mem_univ j.1)
  have hcoup : couplingIn J S j.1.1 = 0 := if_neg j.2
  rw [hcoup, mul_zero]
  have hpos : 1 ≤ reEdge G S (a, b) j.1 := by rw [reEdge_apply, dif_neg j.2]; convert hj
  rw [zero_pow (by omega), zero_div]


theorem currentSum_couplingIn_eq (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (A : Finset V) :
    currentSum G β (couplingIn J S) A
      = ∑' a : {i : ↥G.edgeFinset // isIn G S i} → ℕ,
          (if sources G (ofEdgeFun G (aFull G S a)) = A
            then weight G β J (ofEdgeFun G (aFull G S a)) else 0) := by
  unfold currentSum
  rw [← (Equiv.piEquivPiSubtypeProd (isIn G S) (fun _ => ℕ)).symm.tsum_eq]
  rw [Summable.tsum_prod ?_]
  · refine tsum_congr (fun a => ?_)
    rw [tsum_eq_single (fun _ => 0) ?_]
    · show (if sources G (ofEdgeFun G (reEdge G S (a, fun _ => 0))) = A
              then weight G β (couplingIn J S) (ofEdgeFun G (reEdge G S (a, fun _ => 0))) else 0) = _
      rw [reEdge_zero_right]
      by_cases hA : sources G (ofEdgeFun G (aFull G S a)) = A
      · rw [if_pos hA, if_pos hA, weight_couplingIn_aFull]
      · rw [if_neg hA, if_neg hA]
    · intro b hb
      have hex : ∃ j, 1 ≤ b j := by
        by_contra hc; push Not at hc
        exact hb (funext (fun j => by have := hc j; omega))
      obtain ⟨j, hj⟩ := hex
      show (if sources G (ofEdgeFun G (reEdge G S (a, b))) = A
              then weight G β (couplingIn J S) (ofEdgeFun G (reEdge G S (a, b))) else 0) = 0
      rw [weight_reEdge_eq_zero G β J S a b j hj]; simp
  · have hsum := (summable_norm_currentSum_summand G β (couplingIn J S) A).of_norm
    rw [← (Equiv.piEquivPiSubtypeProd (isIn G S) (fun _ => ℕ)).symm.summable_iff
      (f := fun m => if sources G (ofEdgeFun G m) = A then weight G β (couplingIn J S) (ofEdgeFun G m)
        else 0)] at hsum
    exact hsum


theorem aFull_injective (S : Finset V) : Function.Injective (aFull G S) := by
  intro a a' h; funext i
  have hh := congrFun h i.1
  unfold aFull at hh; rw [dif_pos i.2, dif_pos i.2] at hh; convert hh

theorem bFull_injective (S : Finset V) : Function.Injective (bFull G S) := by
  intro b b' h; funext i
  have hh := congrFun h i.1
  unfold bFull at hh; rw [dif_neg i.2, dif_neg i.2] at hh; convert hh


theorem summable_norm_weight_aFull (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) :
    Summable (fun a : {i : ↥G.edgeFinset // isIn G S i} → ℕ =>
      ‖weight G β J (ofEdgeFun G (aFull G S a))‖) :=
  (summable_norm_weight_ofEdgeFun G β J).comp_injective (aFull_injective G S)


theorem summable_norm_weight_bFull (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) :
    Summable (fun b : {i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ =>
      ‖weight G β J (ofEdgeFun G (bFull G S b))‖) :=
  (summable_norm_weight_ofEdgeFun G β J).comp_injective (bFull_injective G S)


theorem summand_factor (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (P : Current V → Prop)
    [DecidablePred P]
    (H1 : ∀ m, P m → NoCrossing G m S)
    (H2 : ∀ m m' : Current V, (∀ i ∈ G.edgeFinset, ¬ edgeInside S i → m i = m' i) → (P m ↔ P m'))
    (A : Finset V) (hAS : A ⊆ S)
    (a : {i : ↥G.edgeFinset // isIn G S i} → ℕ) (b : {i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ)
    (n₂ : ↥G.edgeFinset → ℕ) :
    (if sources G (ofEdgeFun G (reEdge G S (a, b))) = A then
        weight G β J (ofEdgeFun G (reEdge G S (a, b))) else 0)
      * (if sources G (ofEdgeFun G n₂) = ∅ then weight G β J (ofEdgeFun G n₂) else 0)
      * (if P (fun e => ofEdgeFun G (reEdge G S (a, b)) e + ofEdgeFun G n₂ e) then 1 else 0)
    = (if sources G (ofEdgeFun G (aFull G S a)) = A then
        weight G β J (ofEdgeFun G (aFull G S a)) else 0)
      * ((if sources G (ofEdgeFun G (bFull G S b)) = ∅ then weight G β J (ofEdgeFun G (bFull G S b)) else 0)
        * (if sources G (ofEdgeFun G n₂) = ∅ then weight G β J (ofEdgeFun G n₂) else 0)
        * (if P (fun e => ofEdgeFun G (bFull G S b) e + ofEdgeFun G n₂ e) then 1 else 0)) := by
  
  have hP : P (fun e => ofEdgeFun G (reEdge G S (a, b)) e + ofEdgeFun G n₂ e)
      ↔ P (fun e => ofEdgeFun G (bFull G S b) e + ofEdgeFun G n₂ e) := by
    apply H2
    intro i _ hi
    
    have : ofEdgeFun G (reEdge G S (a, b)) i = ofEdgeFun G (bFull G S b) i := by
      unfold ofEdgeFun
      by_cases h : i ∈ G.edgeFinset
      · rw [dif_pos h, dif_pos h, reEdge_eq_add, aFull, dif_neg (by unfold isIn; exact hi), zero_add]
      · rw [dif_neg h, dif_neg h]
    rw [this]
  by_cases hev : P (fun e => ofEdgeFun G (bFull G S b) e + ofEdgeFun G n₂ e)
  · 
    rw [if_pos hev, if_pos (hP.mpr hev), mul_one, mul_one]
    
    have hncross : NoCrossing G (fun e => ofEdgeFun G (reEdge G S (a, b)) e + ofEdgeFun G n₂ e) S :=
      H1 _ (hP.mpr (hev))
    
    have hcross : ∀ i : ↥G.edgeFinset, 1 ≤ bFull G S b i → edgeInside Sᶜ (i : Sym2 V) := by
      intro i hipos
      have he : (i : Sym2 V) ∈ G.edgeFinset := i.2
      have hsuper : 1 ≤ (fun e => ofEdgeFun G (reEdge G S (a, b)) e + ofEdgeFun G n₂ e) i.1 := by
        have hge : bFull G S b i ≤ ofEdgeFun G (reEdge G S (a, b)) i.1 := by
          rw [show ofEdgeFun G (reEdge G S (a, b)) i.1 = reEdge G S (a, b) i from by
            unfold ofEdgeFun; rw [dif_pos i.2]]
          rw [reEdge_eq_add]; omega
        simp only; omega
      rcases hncross _ he hsuper with hi | hi
      · 
        exfalso
        have hni : ¬ isIn G S i := by
          intro hii; unfold bFull at hipos; rw [dif_pos hii] at hipos; omega
        exact hni hi
      · exact hi
    
    have haS : sources G (ofEdgeFun G (aFull G S a)) ⊆ S := sources_aFull_subset G S a
    have hbSc : sources G (ofEdgeFun G (bFull G S b)) ⊆ Sᶜ := sources_bFull_subset_compl G S b hcross
    
    have hdisj : Disjoint (sources G (ofEdgeFun G (aFull G S a)))
        (sources G (ofEdgeFun G (bFull G S b))) := by
      refine Finset.disjoint_left.mpr (fun v hva hvb => ?_)
      exact (Finset.mem_compl.mp (hbSc hvb)) (haS hva)
    
    rw [sources_reEdge_split]
    by_cases hcon : sources G (ofEdgeFun G (aFull G S a)) ∆ sources G (ofEdgeFun G (bFull G S b))
        = A
    · 
      have hunion : sources G (ofEdgeFun G (aFull G S a)) ∪ sources G (ofEdgeFun G (bFull G S b))
          = A := by
        rw [← hcon, ← (symmDiff_eq_union_iff _ _).mpr hdisj]
      have hbempty : sources G (ofEdgeFun G (bFull G S b)) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro v hvb
        have hvScompl : v ∈ Sᶜ := hbSc hvb
        have hvA : v ∈ A := by rw [← hunion]; exact Finset.mem_union_right _ hvb
        exact (Finset.mem_compl.mp hvScompl) (hAS hvA)
      have haval : sources G (ofEdgeFun G (aFull G S a)) = A := by
        rw [← hunion, hbempty, Finset.union_empty]
      rw [if_pos hcon, if_pos haval, if_pos hbempty, weight_reEdge_split]; ring
    · 
      rw [if_neg hcon]
      by_cases haval : sources G (ofEdgeFun G (aFull G S a)) = A
      · by_cases hbempty : sources G (ofEdgeFun G (bFull G S b)) = ∅
        · exfalso; apply hcon; rw [haval, hbempty]; simp
        · rw [if_neg hbempty]; ring
      · rw [if_neg haval]; ring
  · 
    rw [if_neg hev, if_neg (fun h => hev (hP.mp h))]
    ring


end Sharpness
end StatMech

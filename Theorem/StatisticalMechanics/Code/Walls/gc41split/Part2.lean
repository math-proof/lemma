/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc41split.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc40count.Part5
import Def.StatisticalMechanics.Code.Walls.gc41split
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.FieldGhostDict

open StatMech.Sharpness.RandomCurrent (sources connK degK compOf switching_card
  exists_conn_set sources_symmDiff path_exists mem_sources)

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


section AbstractPi

variable {E : Type*} [Fintype E] [DecidableEq E] {γ : E → Type*}
  [∀ e, Fintype (γ e)] [∀ e, DecidableEq (γ e)]


theorem gc41_disj_fiberwise (S₁ S₂ : Finset (Σ e : E, γ e)) :
    S₂ ⊆ univ \ S₁ ↔ ∀ e, sigmaFinsetEquivPi S₂ e ⊆ univ \ sigmaFinsetEquivPi S₁ e := by
  constructor
  · intro h e b hb
    rw [gc41_mem_sigmaFinsetEquivPi] at hb
    have := h hb
    simp only [Finset.mem_sdiff, mem_univ, true_and] at this ⊢
    rw [gc41_mem_sigmaFinsetEquivPi]; exact this
  · intro h i hi
    obtain ⟨e, b⟩ := i
    have hmem : b ∈ sigmaFinsetEquivPi S₂ e := by rw [gc41_mem_sigmaFinsetEquivPi]; exact hi
    have := h e hmem
    simp only [Finset.mem_sdiff, mem_univ, true_and] at this ⊢
    rw [gc41_mem_sigmaFinsetEquivPi] at this; exact this


theorem gc41_perFiber_count (α : Type*) [Fintype α] [DecidableEq α] (n k1 k2 : ℕ)
    (h : Fintype.card α = n) :
    #((univ : Finset (Finset α × Finset α)).filter
        (fun p => p.2 ⊆ univ \ p.1 ∧ #p.1 = k1 ∧ #p.2 = k2))
      = n.choose k1 * (n - k1).choose k2 := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun p : Finset α × Finset α => p.1)
    (t := (univ : Finset α).powersetCard k1)
    (by
      intro p hp
      simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at hp
      simp only [mem_coe, mem_powersetCard]
      exact ⟨subset_univ _, hp.2.1⟩)]
  have hinner : ∀ A ∈ (univ : Finset α).powersetCard k1,
      #(((univ : Finset (Finset α × Finset α)).filter
          (fun p => p.2 ⊆ univ \ p.1 ∧ #p.1 = k1 ∧ #p.2 = k2)).filter (fun p => p.1 = A))
        = (n - k1).choose k2 := by
    intro A hA
    rw [mem_powersetCard] at hA
    rw [show (((univ : Finset (Finset α × Finset α)).filter
          (fun p => p.2 ⊆ univ \ p.1 ∧ #p.1 = k1 ∧ #p.2 = k2)).filter (fun p => p.1 = A))
        = ((univ \ A).powersetCard k2).image (fun B => (A, B)) from ?_]
    · rw [card_image_of_injective _ (by intro B1 B2 hB; simpa using hB)]
      rw [card_powersetCard]
      congr 1
      rw [card_univ_diff, h, hA.2]
    · ext ⟨A', B'⟩
      simp only [mem_filter, mem_univ, true_and, mem_image, mem_powersetCard]
      constructor
      · rintro ⟨⟨hsub, _, hB⟩, hA'⟩
        subst hA'
        exact ⟨B', ⟨hsub, hB⟩, rfl⟩
      · rintro ⟨B, ⟨hsub, hB⟩, heq⟩
        rw [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact ⟨⟨hsub, hA.2, hB⟩, rfl⟩
  rw [Finset.sum_congr rfl hinner]
  rw [Finset.sum_const, card_powersetCard, card_univ, h, smul_eq_mul]


theorem gc41_pi_pair_profile_count (K₁ K₂ : E → ℕ) :
    #((univ : Finset (Finset (Σ e : E, γ e) × Finset (Σ e : E, γ e))).filter
        (fun p => p.2 ⊆ univ \ p.1
          ∧ (fun e => #(sigmaFinsetEquivPi p.1 e)) = K₁
          ∧ (fun e => #(sigmaFinsetEquivPi p.2 e)) = K₂))
      = ∏ e : E, ((Fintype.card (γ e)).choose (K₁ e) * (Fintype.card (γ e) - K₁ e).choose (K₂ e)) := by
  rw [show ((univ : Finset (Finset (Σ e : E, γ e) × Finset (Σ e : E, γ e))).filter
        (fun p => p.2 ⊆ univ \ p.1
          ∧ (fun e => #(sigmaFinsetEquivPi p.1 e)) = K₁
          ∧ (fun e => #(sigmaFinsetEquivPi p.2 e)) = K₂))
      = (Fintype.piFinset (fun e => (univ : Finset (Finset (γ e) × Finset (γ e))).filter
          (fun q => q.2 ⊆ univ \ q.1 ∧ #q.1 = K₁ e ∧ #q.2 = K₂ e))).image gc41_pairSigmaEquivPi.symm
      from ?_]
  · rw [card_image_of_injective _ gc41_pairSigmaEquivPi.symm.injective, Fintype.card_piFinset]
    refine Finset.prod_congr rfl (fun e _ => ?_)
    exact gc41_perFiber_count (γ e) (Fintype.card (γ e)) (K₁ e) (K₂ e) rfl
  · ext ⟨S₁, S₂⟩
    simp only [Finset.mem_filter, mem_univ, true_and, mem_image, Fintype.mem_piFinset]
    constructor
    · rintro ⟨hdisj, hp1, hp2⟩
      refine ⟨gc41_pairSigmaEquivPi (S₁, S₂), ?_, ?_⟩
      · intro e
        simp only [gc41_pairSigmaEquivPi, Equiv.coe_fn_mk, Finset.mem_filter, mem_univ, true_and]
        exact ⟨(gc41_disj_fiberwise S₁ S₂).mp hdisj e, congrFun hp1 e, congrFun hp2 e⟩
      · rw [Equiv.symm_apply_apply]
    · rintro ⟨f, hf, heq⟩
      have hS1 : S₁ = (gc41_pairSigmaEquivPi.symm f).1 := (congrArg Prod.fst heq).symm
      have hS2 : S₂ = (gc41_pairSigmaEquivPi.symm f).2 := (congrArg Prod.snd heq).symm
      subst hS1 hS2
      have hval1 : ∀ e, sigmaFinsetEquivPi (gc41_pairSigmaEquivPi.symm f).1 e = (f e).1 := by
        intro e
        show sigmaFinsetEquivPi (sigmaFinsetEquivPi.symm (fun e => (f e).1)) e = (f e).1
        rw [Equiv.apply_symm_apply]
      have hval2 : ∀ e, sigmaFinsetEquivPi (gc41_pairSigmaEquivPi.symm f).2 e = (f e).2 := by
        intro e
        show sigmaFinsetEquivPi (sigmaFinsetEquivPi.symm (fun e => (f e).2)) e = (f e).2
        rw [Equiv.apply_symm_apply]
      refine ⟨?_, ?_, ?_⟩
      · rw [gc41_disj_fiberwise]
        intro e
        have := hf e
        simp only [Finset.mem_filter, mem_univ, true_and] at this
        rw [hval1 e, hval2 e]; exact this.1
      · funext e
        have := hf e
        simp only [Finset.mem_filter, mem_univ, true_and] at this
        show #(sigmaFinsetEquivPi (gc41_pairSigmaEquivPi.symm f).1 e) = K₁ e
        rw [hval1 e]; exact this.2.1
      · funext e
        have := hf e
        simp only [Finset.mem_filter, mem_univ, true_and] at this
        show #(sigmaFinsetEquivPi (gc41_pairSigmaEquivPi.symm f).2 e) = K₂ e
        rw [hval2 e]; exact this.2.2

end AbstractPi


theorem gc41_pair_profile_count (m : ↥G.edgeFinset → ℕ) (K₁ K₂ : ↥G.edgeFinset → ℕ) :
    #((univ : Finset (Finset (Copy G m) × Finset (Copy G m))).filter
        (fun p => p.2 ⊆ univ \ p.1
          ∧ profileFlux G m p.1 = K₁ ∧ profileFlux G m p.2 = K₂))
      = ∏ e : ↥G.edgeFinset, ((m e).choose (K₁ e) * (m e - K₁ e).choose (K₂ e)) := by
  have hprof : ∀ (S : Finset (Copy G m)),
      profileFlux G m S = fun e => #(sigmaFinsetEquivPi S e) := by
    intro S; funext e; rw [sigmaFinsetEquivPi_apply_card]; rfl
  rw [show ((univ : Finset (Finset (Copy G m) × Finset (Copy G m))).filter
        (fun p => p.2 ⊆ univ \ p.1
          ∧ profileFlux G m p.1 = K₁ ∧ profileFlux G m p.2 = K₂))
      = ((univ : Finset (Finset (Copy G m) × Finset (Copy G m))).filter
        (fun p => p.2 ⊆ univ \ p.1
          ∧ (fun e => #(sigmaFinsetEquivPi p.1 e)) = K₁
          ∧ (fun e => #(sigmaFinsetEquivPi p.2 e)) = K₂)) from by
    apply Finset.filter_congr
    intro p _
    rw [hprof p.1, hprof p.2]]
  rw [gc41_pi_pair_profile_count K₁ K₂]
  exact Finset.prod_congr rfl (fun e _ => by rw [Fintype.card_fin])


theorem gc41_pairProfile_le (m : ↥G.edgeFinset → ℕ) (S₁ S₂ : Finset (Copy G m))
    (hdisj : S₂ ⊆ univ \ S₁) :
    ∀ e, profileFlux G m S₁ e + profileFlux G m S₂ e ≤ m e := by
  intro e
  have hd : Disjoint (S₁.filter (fun i : Copy G m => i.1 = e))
      (S₂.filter (fun i : Copy G m => i.1 = e)) := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    simp only [mem_filter] at hi1 hi2
    have := hdisj hi2.1
    rw [mem_sdiff] at this
    exact this.2 hi1.1
  unfold profileFlux
  rw [← Finset.card_union_of_disjoint hd, ← fiber_card G m e]
  apply Finset.card_le_card
  intro i hi
  rw [mem_union, mem_filter, mem_filter] at hi
  simp only [mem_filter, mem_univ, true_and]
  rcases hi with ⟨_, he⟩ | ⟨_, he⟩ <;> exact he


theorem gc41_fin_filter_range_card (n a b : ℕ) (h : a + b ≤ n) :
    #((univ : Finset (Fin n)).filter (fun j => a ≤ j.val ∧ j.val < a + b)) = b := by
  rw [show ((univ : Finset (Fin n)).filter (fun j => a ≤ j.val ∧ j.val < a + b))
        = (Finset.Ico a (a + b)).attachFin (by intro k hk; rw [mem_Ico] at hk; omega) from ?_]
  · rw [Finset.card_attachFin, Nat.card_Ico]; omega
  · ext j
    simp only [mem_filter, mem_univ, true_and, Finset.mem_attachFin, mem_Ico]


theorem gc41_profile_range (m : ↥G.edgeFinset → ℕ) (K₁ K₂ : ↥G.edgeFinset → ℕ)
    (hK : ∀ e, K₁ e + K₂ e ≤ m e) :
    profileFlux G m (univ.filter (fun i : FluxEdgeCopy.Copy G m =>
        K₁ i.1 ≤ i.2.val ∧ i.2.val < K₁ i.1 + K₂ i.1))
      = K₂ := by
  funext e
  unfold profileFlux
  rw [show (univ.filter (fun i : FluxEdgeCopy.Copy G m =>
            K₁ i.1 ≤ i.2.val ∧ i.2.val < K₁ i.1 + K₂ i.1)).filter
          (fun i : FluxEdgeCopy.Copy G m => i.1 = e)
        = ((univ : Finset (Fin (m e))).filter (fun j => K₁ e ≤ j.val ∧ j.val < K₁ e + K₂ e)).image
            (fun j => (⟨e, j⟩ : FluxEdgeCopy.Copy G m)) from ?_]
  · rw [Finset.card_image_of_injective _ (by intro j₁ j₂ h; simpa using h)]
    exact gc41_fin_filter_range_card (m e) (K₁ e) (K₂ e) (hK e)
  · ext i
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · rintro ⟨⟨hlo, hhi⟩, he⟩; subst he; exact ⟨i.2, ⟨hlo, hhi⟩, rfl⟩
    · rintro ⟨j, ⟨hlo, hhi⟩, he⟩; subst he; exact ⟨⟨hlo, hhi⟩, rfl⟩


theorem gc41_pair_edgecopy_bridge {M : Type*} [AddCommMonoid M]
    (m : ↥G.edgeFinset → ℕ)
    (Θ : (↥G.edgeFinset → ℕ) → (↥G.edgeFinset → ℕ) → M) :
    (∑ K : {pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e},
        (∏ e : ↥G.edgeFinset, ((m e).choose (K.1.1 e) * (m e - K.1.1 e).choose (K.1.2 e)))
          • Θ K.1.1 K.1.2)
      = ∑ p ∈ (univ : Finset (Finset (Copy G m) × Finset (Copy G m))).filter
          (fun p => p.2 ⊆ univ \ p.1),
          Θ (profileFlux G m p.1) (profileFlux G m p.2) := by
  classical
  set T := {pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e} with hT
  set g : Finset (Copy G m) × Finset (Copy G m) → T := fun p =>
    if hp : p.2 ⊆ univ \ p.1
    then ⟨(profileFlux G m p.1, profileFlux G m p.2), gc41_pairProfile_le G m p.1 p.2 hp⟩
    else ⟨(fun _ => 0, fun _ => 0), fun e => by simp⟩ with hg
  have hΘ : ∀ p ∈ (univ : Finset (Finset (Copy G m) × Finset (Copy G m))).filter
        (fun p => p.2 ⊆ univ \ p.1),
      Θ (profileFlux G m p.1) (profileFlux G m p.2) = (fun K : T => Θ K.1.1 K.1.2) (g p) := by
    intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp
    simp only [hg, hp, dif_pos]
  rw [Finset.sum_congr rfl hΘ, Finset.sum_comp (fun K : T => Θ K.1.1 K.1.2) g]
  
  have himg : (((univ : Finset (Finset (Copy G m) × Finset (Copy G m))).filter
        (fun p => p.2 ⊆ univ \ p.1)).image g) = univ := by
    apply Finset.eq_univ_of_forall
    intro K
    rw [mem_image]
    refine ⟨(univ.filter (fun i : FluxEdgeCopy.Copy G m => i.2.val < K.1.1 i.1),
             univ.filter (fun i : FluxEdgeCopy.Copy G m =>
                K.1.1 i.1 ≤ i.2.val ∧ i.2.val < K.1.1 i.1 + K.1.2 i.1)),
           ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and]
      intro i hi
      simp only [mem_filter, mem_univ, true_and] at hi
      rw [mem_sdiff]
      refine ⟨mem_univ _, ?_⟩
      simp only [mem_filter, mem_univ, true_and]
      omega
    · have hdisj : (univ.filter (fun i : FluxEdgeCopy.Copy G m => K.1.1 i.1 ≤ i.2.val
              ∧ i.2.val < K.1.1 i.1 + K.1.2 i.1)) ⊆ univ \
            (univ.filter (fun i : FluxEdgeCopy.Copy G m => i.2.val < K.1.1 i.1)) := by
        intro i hi
        simp only [mem_filter, mem_univ, true_and] at hi
        rw [mem_sdiff]
        refine ⟨mem_univ _, ?_⟩
        simp only [mem_filter, mem_univ, true_and]
        omega
      have hK1le : K.1.1 ≤ m := by
        intro e; exact le_trans (Nat.le_add_right _ _) (K.2 e)
      simp only [hg, hdisj, dif_pos]
      rw [Subtype.ext_iff, Prod.ext_iff]
      refine ⟨?_, ?_⟩
      · exact profileFlux_surj G m K.1.1 hK1le
      · exact gc41_profile_range G m K.1.1 K.1.2 K.2
  rw [himg]
  refine Finset.sum_congr rfl (fun K _ => ?_)
  rw [show #(((univ : Finset (Finset (Copy G m) × Finset (Copy G m))).filter
        (fun p => p.2 ⊆ univ \ p.1)).filter (fun p => g p = K))
      = #((univ : Finset (Finset (Copy G m) × Finset (Copy G m))).filter
        (fun p => p.2 ⊆ univ \ p.1
          ∧ profileFlux G m p.1 = K.1.1 ∧ profileFlux G m p.2 = K.1.2)) from ?_]
  · rw [gc41_pair_profile_count G m K.1.1 K.1.2]
  · congr 1
    ext p
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hp, hgp⟩
      simp only [hg, hp, dif_pos] at hgp
      rw [Subtype.ext_iff, Prod.ext_iff] at hgp
      exact ⟨hp, hgp.1, hgp.2⟩
    · rintro ⟨hp, h1, h2⟩
      refine ⟨hp, ?_⟩
      simp only [hg, hp, dif_pos]
      rw [Subtype.ext_iff, Prod.ext_iff]
      exact ⟨h1, h2⟩


theorem gc41_tpsum_eq_pairCount (β : ℝ) (J : Sym2 V → ℝ) (m : ↥G.edgeFinset → ℕ) (A B : Finset V) :
    gc15_tpsum G β J m A B
      = (#((univ : Finset (Finset (Copy G m) × Finset (Copy G m))).filter
          (fun p => p.2 ⊆ univ \ p.1
            ∧ RandomCurrent.sources (endsM G m) p.1 = A
            ∧ RandomCurrent.sources (endsM G m) p.2 = B)) : ℝ)
        * weight G β J (ofEdgeFun G m) := by
  unfold gc15_tpsum
  have hstep : ∀ K : {pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e},
      (if sources G (ofEdgeFun G K.1.1) = A then weight G β J (ofEdgeFun G K.1.1) else 0)
        * (if sources G (ofEdgeFun G K.1.2) = B then weight G β J (ofEdgeFun G K.1.2) else 0)
        * weight G β J (ofEdgeFun G (fun e => m e - K.1.1 e - K.1.2 e))
      = (∏ e : ↥G.edgeFinset, ((m e).choose (K.1.1 e) * (m e - K.1.1 e).choose (K.1.2 e)))
        • ((if sources G (ofEdgeFun G K.1.1) = A then (1:ℝ) else 0)
            * (if sources G (ofEdgeFun G K.1.2) = B then 1 else 0)
            * weight G β J (ofEdgeFun G m)) := by
    intro K
    rw [nsmul_eq_mul, Nat.cast_prod]
    by_cases hA : sources G (ofEdgeFun G K.1.1) = A
    · by_cases hB : sources G (ofEdgeFun G K.1.2) = B
      · have hprod : (∏ e ∈ G.edgeFinset, ((Nat.choose ((ofEdgeFun G m) e) ((ofEdgeFun G K.1.1) e) : ℝ)
                  * (Nat.choose ((ofEdgeFun G m) e - (ofEdgeFun G K.1.1) e) ((ofEdgeFun G K.1.2) e) : ℝ)))
              = (∏ e : ↥G.edgeFinset, ((m e).choose (K.1.1 e) * (m e - K.1.1 e).choose (K.1.2 e) : ℝ)) := by
          rw [← Finset.prod_attach G.edgeFinset
            (fun e => ((Nat.choose ((ofEdgeFun G m) e) ((ofEdgeFun G K.1.1) e) : ℝ)
                * (Nat.choose ((ofEdgeFun G m) e - (ofEdgeFun G K.1.1) e) ((ofEdgeFun G K.1.2) e) : ℝ)))]
          refine Finset.prod_congr rfl (fun e _ => ?_)
          simp only [ofEdgeFun, e.2, dif_pos]
        rw [if_pos hA, if_pos hB, if_pos hA, if_pos hB,
          weight_split₃_eq_binom G β J m K.1.1 K.1.2 K.2, hprod]
        push_cast; ring
      · rw [if_neg hB]; simp [hB]
    · rw [if_neg hA]; simp [hA]
  simp_rw [hstep]
  rw [gc41_pair_edgecopy_bridge G m (fun K₁ K₂ =>
    (if sources G (ofEdgeFun G K₁) = A then (1:ℝ) else 0)
      * (if sources G (ofEdgeFun G K₂) = B then 1 else 0)
      * weight G β J (ofEdgeFun G m))]
  rw [Finset.card_filter, Finset.sum_filter]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [← FluxEdgeCopy.sources_eq, ← FluxEdgeCopy.sources_eq]
  by_cases hd : p.2 ⊆ univ \ p.1 <;>
    by_cases hA : RandomCurrent.sources (endsM G m) p.1 = A <;>
    by_cases hB : RandomCurrent.sources (endsM G m) p.2 = B <;>
    simp [hd, hA, hB]


theorem gc41_sd_third {W : Type*} [DecidableEq W] (o x y g : W)
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g) :
    ({o, x, y, g} : Finset W) ∆ {o, g} ∆ {x, g} = ({y, g} : Finset W) := by
  ext a
  simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  by_cases h1 : a = o <;> by_cases h2 : a = x <;> by_cases h3 : a = y <;> by_cases h4 : a = g <;>
    subst_vars <;> simp_all


theorem gc41_pairCount_eq_NR {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
    (ends : ι → Sym2 W) {o x y g : W}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W)) :
    #((univ : Finset (Finset ι × Finset ι)).filter
        (fun p => p.2 ⊆ univ \ p.1
          ∧ sources ends p.1 = ({o, g} : Finset W)
          ∧ sources ends p.2 = ({x, g} : Finset W)))
      = gc40_NR ends o x y g := by
  unfold gc40_NR
  congr 1
  apply Finset.filter_congr
  intro p _
  constructor
  · rintro ⟨hd, h1, h2⟩
    refine ⟨hd, h1, h2, ?_⟩
    have hcompl : (univ \ p.1) \ p.2 = (univ \ p.1) ∆ p.2 := (symmDiff_of_ge hd).symm
    rw [hcompl, sources_symmDiff, gc40_sources_compl, huniv, h1, h2,
      gc41_sd_third o x y g hox hoy hog hxy hxg hyg]
  · rintro ⟨hd, h1, h2, _⟩; exact ⟨hd, h1, h2⟩


theorem gc41_NR_eq_zero {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
    (ends : ι → Sym2 W) {o x y g : W}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) ≠ ({o, x, y, g} : Finset W)) :
    gc40_NR ends o x y g = 0 := by
  unfold gc40_NR
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨S₁, S₂⟩ hmem
  simp only [mem_univ, forall_true_left]
  rintro ⟨hd, h1, h2, h3⟩
  apply huniv
  have e1 : sources ends (univ \ S₁) = sources ends univ ∆ sources ends S₁ := gc40_sources_compl ends S₁
  have hcompl : (univ \ S₁) \ S₂ = (univ \ S₁) ∆ S₂ := (symmDiff_of_ge hd).symm
  have e2 : sources ends ((univ \ S₁) \ S₂) = sources ends (univ \ S₁) ∆ sources ends S₂ := by
    rw [hcompl, sources_symmDiff]
  rw [e1, h1] at e2
  rw [h2, h3] at e2
  rw [Finset.ext_iff] at e2 ⊢
  intro a
  have ea := e2 a
  simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton] at ea ⊢
  by_cases h1' : a = o <;> by_cases h2' : a = x <;> by_cases h3' : a = y <;> by_cases h4' : a = g <;>
    subst_vars <;> simp_all


theorem gc41_csTriple_eq_NRsum (β h : ℝ) (o x y : V) (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    gc39_csTriple G β h o x y
      = ∑' m : ↥(withGhost G).edgeFinset → ℕ,
          (gc40_NR (endsM (withGhost G) m) (some o) (some x) (some y) none : ℝ)
            * weight (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) m) := by
  set J' := ghostCoupling h β (fun _ => 1) with hJ'
  set W := withGhost G with hW
  unfold gc39_csTriple
  rw [← sourceTripleSum_eq_mul W β J' ({some o, none}) ({some x, none}) ({some y, none})]
  rw [gc15_sourceTripleSum_eq_tFiber W β J' ({some o, none}) ({some x, none}) ({some y, none})]
  refine tsum_congr (fun m => ?_)
  unfold gc15_tFiber
  rw [gc15_sd4 (some o) (some x) (some y) none (by simp [hox]) (by simp [hoy]) (by simp)
    (by simp [hxy]) (by simp) (by simp)]
  have huniv : RandomCurrent.sources (endsM W m) univ
      = Sharpness.sources W (ofEdgeFun W m) := by
    rw [FluxEdgeCopy.sources_eq, FluxEdgeCopy.profileFlux_univ]
  by_cases hm : Sharpness.sources W (ofEdgeFun W m)
      = ({some o, some x, some y, none} : Finset (Option V))
  · rw [if_pos hm, gc41_tpsum_eq_pairCount W β J' m ({some o, none}) ({some x, none})]
    rw [gc41_pairCount_eq_NR (endsM W m) (o := some o) (x := some x) (y := some y) (g := none)
        (by simp [hox]) (by simp [hoy]) (by simp) (by simp [hxy]) (by simp) (by simp)
        (by rw [huniv]; exact hm)]
  · rw [if_neg hm]
    rw [gc41_NR_eq_zero (endsM W m) (o := some o) (x := some x) (y := some y) (g := none)
        (by simp [hox]) (by simp [hoy]) (by simp) (by simp [hxy]) (by simp) (by simp)
        (by rw [huniv]; exact hm)]
    simp


end StatMech.Walls

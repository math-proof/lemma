/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc85bthreereplicaswitch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc83crosspairing.Part3
import Def.StatisticalMechanics.Code.Walls.gc85bthreereplicaswitch.Part2
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.RandomCurrent StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap


variable {ι : Type*} [DecidableEq ι] [Fintype ι]

variable {W : Type*} [DecidableEq W] [Fintype W]


theorem gc85b_pcount_reroute_eq (ends : ι → Sym2 W) (m : Finset ι) (A B : Finset W)
    {u v : W} (huv : u ≠ v) (P : Finset ι) (hPm : P ⊆ m) (hPsrc : sources ends P = {u, v}) :
    
    
    #((m.powerset ×ˢ m.powerset).filter
        (fun KK => Disjoint KK.1 KK.2 ∧ Disjoint KK.1 P
          ∧ sources ends KK.1 = A ∧ sources ends KK.2 = B ∆ {u, v}))
      = #((m.powerset ×ˢ m.powerset).filter
        (fun KK => Disjoint KK.1 KK.2 ∧ Disjoint KK.1 P
          ∧ sources ends KK.1 = A ∧ sources ends KK.2 = B)) := by
  
  apply Finset.card_bij (fun KK _ => (KK.1, KK.2 ∆ P))
  · 
    rintro ⟨K₁, K₂⟩ hKK
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hKK ⊢
    obtain ⟨⟨hK₁m, hK₂m⟩, hdis, hdisP, hK₁src, hK₂src⟩ := hKK
    refine ⟨⟨hK₁m, ?_⟩, ?_, hdisP, hK₁src, ?_⟩
    · 
      intro a ha
      rw [Finset.mem_symmDiff] at ha
      rcases ha with ⟨h, _⟩ | ⟨h, _⟩
      · exact hK₂m h
      · exact hPm h
    · 
      rw [Finset.disjoint_left] at hdis hdisP ⊢
      intro a haK₁ ha
      rw [Finset.mem_symmDiff] at ha
      rcases ha with ⟨h, _⟩ | ⟨h, _⟩
      · exact hdis haK₁ h
      · exact hdisP haK₁ h
    · 
      rw [sources_symmDiff, hK₂src, hPsrc, symmDiff_symmDiff_cancel_right]
  · 
    rintro ⟨K₁, K₂⟩ hKK ⟨L₁, L₂⟩ hLL heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨h1, h2⟩ := heq
    have : (K₂ ∆ P) ∆ P = (L₂ ∆ P) ∆ P := by rw [h2]
    rw [symmDiff_symmDiff_cancel_right, symmDiff_symmDiff_cancel_right] at this
    rw [h1, this]
  · 
    rintro ⟨L₁, L₂⟩ hLL
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hLL
    obtain ⟨⟨hL₁m, hL₂m⟩, hdis, hdisP, hL₁src, hL₂src⟩ := hLL
    refine ⟨(L₁, L₂ ∆ P), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset]
      refine ⟨⟨hL₁m, ?_⟩, ?_, hdisP, hL₁src, ?_⟩
      · intro a ha
        rw [Finset.mem_symmDiff] at ha
        rcases ha with ⟨h, _⟩ | ⟨h, _⟩
        · exact hL₂m h
        · exact hPm h
      · rw [Finset.disjoint_left] at hdis hdisP ⊢
        intro a haL₁ ha
        rw [Finset.mem_symmDiff] at ha
        rcases ha with ⟨h, _⟩ | ⟨h, _⟩
        · exact hdis haL₁ h
        · exact hdisP haL₁ h
      · rw [sources_symmDiff, hL₂src, hPsrc]
    · simp only [Prod.mk.injEq, true_and]
      rw [symmDiff_symmDiff_cancel_right]


open StatMech.Sharpness.FluxEdgeCopy


theorem gc85b_pcount_univ_mem {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (m : ↥G.edgeFinset → ℕ) (A B : Finset V) (S₁ S₂ : Finset (Copy G m)) :
    (S₁, S₂) ∈ ((univ : Finset (Copy G m)).powerset ×ˢ (univ : Finset (Copy G m)).powerset).filter
        (fun KK => Disjoint KK.1 KK.2 ∧ RandomCurrent.sources (endsM G m) KK.1 = A
          ∧ RandomCurrent.sources (endsM G m) KK.2 = B)
      ↔ (Disjoint S₁ S₂ ∧ RandomCurrent.sources (endsM G m) S₁ = A
          ∧ RandomCurrent.sources (endsM G m) S₂ = B) := by
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset, Finset.subset_univ,
    true_and]


theorem gc85b_profile_add_le {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (m : ↥G.edgeFinset → ℕ) {S₁ S₂ : Finset (Copy G m)}
    (hdis : Disjoint S₁ S₂) (e : ↥G.edgeFinset) :
    profileFlux G m S₁ e + profileFlux G m S₂ e ≤ m e := by
  unfold profileFlux
  rw [← fiber_card G m e, ← Finset.card_union_of_disjoint]
  · apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_union, Finset.mem_filter, mem_univ, true_and] at hi ⊢
    rcases hi with ⟨_, h⟩ | ⟨_, h⟩ <;> exact h
  · exact Finset.disjoint_filter_filter hdis


theorem gc85b_fiber_pair_count {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (m : ↥G.edgeFinset → ℕ) (e : ↥G.edgeFinset) (a b : ℕ) (hab : a + b ≤ m e) :
    #((univ : Finset (Finset (Fin (m e)) × Finset (Fin (m e)))).filter
        (fun st => Disjoint st.1 st.2 ∧ #st.1 = a ∧ #st.2 = b))
      = (m e).choose a * (m e - a).choose b := by
  classical
  set n := m e with hn
  have hemb_inj : Function.Injective
      (fun x : (Σ _s : Finset (Fin n), Finset (Fin n)) => (x.1, x.2)) := by
    rintro ⟨s, t⟩ ⟨s', t'⟩ h
    simp only [Prod.mk.injEq] at h
    exact Sigma.ext h.1 (heq_of_eq h.2)
  
  rw [show ((univ : Finset (Finset (Fin n) × Finset (Fin n))).filter
        (fun st => Disjoint st.1 st.2 ∧ #st.1 = a ∧ #st.2 = b))
      = (Finset.sigma (Finset.powersetCard a (univ : Finset (Fin n)))
          (fun s : Finset (Fin n) => Finset.powersetCard b (sᶜ))).map ⟨_, hemb_inj⟩ from ?_]
  · rw [Finset.card_map, Finset.card_sigma]
    rw [Finset.sum_congr rfl (fun s hs => ?_)]
    · rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul]
    · rw [Finset.mem_powersetCard] at hs
      rw [Finset.card_powersetCard, Finset.card_compl, Fintype.card_fin, hs.2]
  · ext ⟨s, t⟩
    simp only [Finset.mem_filter, mem_univ, true_and, Finset.mem_map, Finset.mem_sigma,
      Finset.mem_powersetCard, Finset.subset_univ, Function.Embedding.coeFn_mk, Sigma.exists,
      Prod.mk.injEq]
    constructor
    · rintro ⟨hdis, hsa, htb⟩
      have hcompl : t ⊆ sᶜ := by
        intro z hz
        rw [Finset.mem_compl]
        exact fun hzs => (Finset.disjoint_left.1 hdis) hzs hz
      refine ⟨s, t, ⟨hsa, hcompl, htb⟩, ?_, ?_⟩ <;> rfl
    · rintro ⟨s', t', ⟨hsa, hts, htb⟩, hse, hte⟩
      subst hse; subst hte
      refine ⟨?_, hsa, htb⟩
      rw [Finset.disjoint_left]
      intro z hz hzt
      exact (Finset.mem_compl.1 (hts hzt)) hz


theorem gc85b_pair_preimage_count {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (m : ↥G.edgeFinset → ℕ) (K₁ K₂ : ↥G.edgeFinset → ℕ)
    (hK : ∀ e, K₁ e + K₂ e ≤ m e) :
    #((univ : Finset (Finset (Copy G m) × Finset (Copy G m))).filter
        (fun SS => Disjoint SS.1 SS.2 ∧ profileFlux G m SS.1 = K₁ ∧ profileFlux G m SS.2 = K₂))
      = ∏ e : ↥G.edgeFinset, (m e).choose (K₁ e) * (m e - K₁ e).choose (K₂ e) := by
  classical
  
  
  rw [show #((univ : Finset (Finset (Copy G m) × Finset (Copy G m))).filter
        (fun SS => Disjoint SS.1 SS.2 ∧ profileFlux G m SS.1 = K₁ ∧ profileFlux G m SS.2 = K₂))
      = #((univ : Finset ((Π e : ↥G.edgeFinset, Finset (Fin (m e)))
            × (Π e : ↥G.edgeFinset, Finset (Fin (m e))))).filter
          (fun ff => (∀ e, Disjoint (ff.1 e) (ff.2 e))
            ∧ (fun e => #(ff.1 e)) = K₁ ∧ (fun e => #(ff.2 e)) = K₂)) from ?_]
  · 
    rw [show #((univ : Finset ((Π e : ↥G.edgeFinset, Finset (Fin (m e)))
            × (Π e : ↥G.edgeFinset, Finset (Fin (m e))))).filter
          (fun ff => (∀ e, Disjoint (ff.1 e) (ff.2 e))
            ∧ (fun e => #(ff.1 e)) = K₁ ∧ (fun e => #(ff.2 e)) = K₂))
        = #(Fintype.piFinset (fun e =>
            ((univ : Finset (Finset (Fin (m e)) × Finset (Fin (m e)))).filter
              (fun st => Disjoint st.1 st.2 ∧ #st.1 = K₁ e ∧ #st.2 = K₂ e)))) from ?_]
    · rw [Fintype.card_piFinset]
      refine Finset.prod_congr rfl (fun e _ => ?_)
      rw [← gc85b_fiber_pair_count G m e (K₁ e) (K₂ e) (hK e)]
    · apply Finset.card_bij (fun ff _ => fun e => (ff.1 e, ff.2 e))
      · rintro ⟨f₁, f₂⟩ hff
        simp only [Finset.mem_filter, mem_univ, true_and] at hff
        obtain ⟨hdis, hc1, hc2⟩ := hff
        simp only [Fintype.mem_piFinset, Finset.mem_filter, mem_univ, true_and]
        intro e
        exact ⟨hdis e, congrFun hc1 e, congrFun hc2 e⟩
      · rintro ⟨f₁, f₂⟩ _ ⟨g₁, g₂⟩ _ h
        simp only at h
        refine Prod.ext ?_ ?_
        · funext e; exact congrArg Prod.fst (congrFun h e)
        · funext e; exact congrArg Prod.snd (congrFun h e)
      · intro g hg
        simp only [Fintype.mem_piFinset, Finset.mem_filter, mem_univ, true_and] at hg
        refine ⟨(fun e => (g e).1, fun e => (g e).2), ?_, ?_⟩
        · simp only [Finset.mem_filter, mem_univ, true_and]
          refine ⟨fun e => (hg e).1, ?_, ?_⟩
          · funext e; exact (hg e).2.1
          · funext e; exact (hg e).2.2
        · funext e; rfl
  · 
    apply Finset.card_bij (fun SS _ => (sigmaFinsetEquivPi SS.1, sigmaFinsetEquivPi SS.2))
    · rintro ⟨S₁, S₂⟩ hSS
      simp only [Finset.mem_filter, mem_univ, true_and] at hSS ⊢
      obtain ⟨hdis, hp1, hp2⟩ := hSS
      refine ⟨?_, ?_, ?_⟩
      · intro e
        rw [Finset.disjoint_left]
        intro a ha hb
        simp only [sigmaFinsetEquivPi, Equiv.coe_fn_mk, Finset.mem_filter, mem_univ, true_and] at ha hb
        rw [Finset.disjoint_left] at hdis
        exact hdis ha hb
      · funext e
        have : profileFlux G m S₁ = fun e => #(sigmaFinsetEquivPi S₁ e) := by
          funext e; rw [sigmaFinsetEquivPi_apply_card]; rfl
        rw [← hp1, this]
      · funext e
        have : profileFlux G m S₂ = fun e => #(sigmaFinsetEquivPi S₂ e) := by
          funext e; rw [sigmaFinsetEquivPi_apply_card]; rfl
        rw [← hp2, this]
    · rintro ⟨S₁, S₂⟩ _ ⟨T₁, T₂⟩ _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (sigmaFinsetEquivPi.injective h.1) (sigmaFinsetEquivPi.injective h.2)
    · rintro ⟨f₁, f₂⟩ hff
      simp only [Finset.mem_filter, mem_univ, true_and] at hff
      obtain ⟨hdis, hc1, hc2⟩ := hff
      refine ⟨(sigmaFinsetEquivPi.symm f₁, sigmaFinsetEquivPi.symm f₂), ?_, ?_⟩
      · simp only [Finset.mem_filter, mem_univ, true_and]
        refine ⟨?_, ?_, ?_⟩
        · rw [Finset.disjoint_left]
          intro a ha hb
          have ha' : a.2 ∈ f₁ a.1 := by
            simp only [sigmaFinsetEquivPi, Equiv.coe_fn_symm_mk, Finset.mem_filter, mem_univ,
              true_and] at ha
            exact ha
          have hb' : a.2 ∈ f₂ a.1 := by
            simp only [sigmaFinsetEquivPi, Equiv.coe_fn_symm_mk, Finset.mem_filter, mem_univ,
              true_and] at hb
            exact hb
          exact (Finset.disjoint_left.1 (hdis a.1)) ha' hb'
        · funext e
          have hpf : profileFlux G m (sigmaFinsetEquivPi.symm f₁)
              = fun e => #(sigmaFinsetEquivPi (sigmaFinsetEquivPi.symm f₁) e) := by
            funext e; rw [sigmaFinsetEquivPi_apply_card]; rfl
          rw [hpf, Equiv.apply_symm_apply, ← hc1]
        · funext e
          have hpf : profileFlux G m (sigmaFinsetEquivPi.symm f₂)
              = fun e => #(sigmaFinsetEquivPi (sigmaFinsetEquivPi.symm f₂) e) := by
            funext e; rw [sigmaFinsetEquivPi_apply_card]; rfl
          rw [hpf, Equiv.apply_symm_apply, ← hc2]
      · simp only [Equiv.apply_symm_apply]


theorem gc85b_triple_bridge {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (m : ↥G.edgeFinset → ℕ)
    (Θ : (↥G.edgeFinset → ℕ) → (↥G.edgeFinset → ℕ) → ℝ) :
    (∑ K : {pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e},
          (∏ e : ↥G.edgeFinset, (m e).choose (K.1.1 e) * (m e - K.1.1 e).choose (K.1.2 e))
            • Θ K.1.1 K.1.2)
      = ∑ SS ∈ (univ : Finset (Finset (Copy G m) × Finset (Copy G m))).filter
          (fun SS => Disjoint SS.1 SS.2),
        Θ (profileFlux G m SS.1) (profileFlux G m SS.2) := by
  classical
  
  have hexp : ∀ K : {pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e},
      (∏ e : ↥G.edgeFinset, (m e).choose (K.1.1 e) * (m e - K.1.1 e).choose (K.1.2 e))
            • Θ K.1.1 K.1.2
      = ∑ SS ∈ (univ : Finset (Finset (Copy G m) × Finset (Copy G m))).filter
          (fun SS => Disjoint SS.1 SS.2 ∧ profileFlux G m SS.1 = K.1.1
            ∧ profileFlux G m SS.2 = K.1.2),
          Θ (profileFlux G m SS.1) (profileFlux G m SS.2) := by
    intro K
    rw [Finset.sum_congr rfl (fun SS hSS => by
        simp only [Finset.mem_filter, mem_univ, true_and] at hSS
        rw [hSS.2.1, hSS.2.2]), Finset.sum_const]
    rw [nsmul_eq_mul, nsmul_eq_mul]
    congr 1
    rw [← gc85b_pair_preimage_count G m K.1.1 K.1.2 K.2]
  rw [Finset.sum_congr rfl (fun K _ => hexp K)]
  
  rw [← Finset.sum_biUnion]
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext SS
    simp only [Finset.mem_biUnion, mem_univ, Finset.mem_filter, true_and]
    constructor
    · rintro ⟨K, hmem⟩; exact hmem.1
    · intro hdis
      exact ⟨⟨(profileFlux G m SS.1, profileFlux G m SS.2),
        fun e => gc85b_profile_add_le G m hdis e⟩, hdis, rfl, rfl⟩
  · 
    intro K₁ _ K₂ _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    rintro SS hSS1 hSS2
    simp only [Finset.mem_filter, mem_univ, true_and] at hSS1 hSS2
    apply hne
    apply Subtype.ext
    apply Prod.ext
    · rw [← hSS1.2.1, ← hSS2.2.1]
    · rw [← hSS1.2.2, ← hSS2.2.2]


theorem gc85b_tpsum_eq_pcount {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (β : ℝ) (J : Sym2 V → ℝ) (m : ↥G.edgeFinset → ℕ) (A B : Finset V) :
    gc15_tpsum G β J m A B
      = (gc85b_pcount (endsM G m) univ A B : ℝ) * weight G β J (ofEdgeFun G m) := by
  classical
  unfold gc15_tpsum gc85b_pcount
  
  have hstep : ∀ K : {pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e},
      (if sources G (ofEdgeFun G K.1.1) = A then weight G β J (ofEdgeFun G K.1.1) else 0)
        * (if sources G (ofEdgeFun G K.1.2) = B then weight G β J (ofEdgeFun G K.1.2) else 0)
        * weight G β J (ofEdgeFun G (fun e => m e - K.1.1 e - K.1.2 e))
      = (∏ e : ↥G.edgeFinset, (m e).choose (K.1.1 e) * (m e - K.1.1 e).choose (K.1.2 e))
          • ((if sources G (ofEdgeFun G K.1.1) = A then (1 : ℝ) else 0)
              * (if sources G (ofEdgeFun G K.1.2) = B then 1 else 0)
              * weight G β J (ofEdgeFun G m)) := by
    intro K
    rw [nsmul_eq_mul, Nat.cast_prod]
    by_cases hA : sources G (ofEdgeFun G K.1.1) = A <;>
      by_cases hB : sources G (ofEdgeFun G K.1.2) = B
    · rw [if_pos hA, if_pos hB, if_pos hA, if_pos hB,
        weight_split₃_eq_binom G β J m K.1.1 K.1.2 K.2]
      rw [show (∏ e ∈ G.edgeFinset,
              ((Nat.choose ((ofEdgeFun G m) e) ((ofEdgeFun G K.1.1) e) : ℝ)
                * (Nat.choose ((ofEdgeFun G m) e - (ofEdgeFun G K.1.1) e) ((ofEdgeFun G K.1.2) e) : ℝ)))
            = (∏ e : ↥G.edgeFinset,
                ((m e).choose (K.1.1 e) * (m e - K.1.1 e).choose (K.1.2 e) : ℝ)) from ?_]
      · push_cast; ring
      · rw [← Finset.prod_attach G.edgeFinset
          (fun e => ((Nat.choose ((ofEdgeFun G m) e) ((ofEdgeFun G K.1.1) e) : ℝ)
            * (Nat.choose ((ofEdgeFun G m) e - (ofEdgeFun G K.1.1) e) ((ofEdgeFun G K.1.2) e) : ℝ)))]
        refine Finset.prod_congr rfl (fun e _ => ?_)
        simp only [ofEdgeFun, dif_pos e.2]
    · rw [if_neg hB]; simp [hB]
    · rw [if_neg hA]; simp [hA]
    · rw [if_neg hA]; simp [hA]
  simp_rw [hstep]
  
  rw [show (∑ K : {pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e},
        (∏ e : ↥G.edgeFinset, (m e).choose (K.1.1 e) * (m e - K.1.1 e).choose (K.1.2 e))
          • ((if sources G (ofEdgeFun G K.1.1) = A then (1 : ℝ) else 0)
              * (if sources G (ofEdgeFun G K.1.2) = B then 1 else 0)
              * weight G β J (ofEdgeFun G m)))
      = ∑ SS ∈ (univ : Finset (Finset (Copy G m) × Finset (Copy G m))).filter
            (fun SS => Disjoint SS.1 SS.2),
          ((if sources G (ofEdgeFun G (profileFlux G m SS.1)) = A then (1 : ℝ) else 0)
              * (if sources G (ofEdgeFun G (profileFlux G m SS.2)) = B then 1 else 0)
              * weight G β J (ofEdgeFun G m)) from
    gc85b_triple_bridge G m (fun K₁ K₂ =>
      (if sources G (ofEdgeFun G K₁) = A then (1 : ℝ) else 0)
        * (if sources G (ofEdgeFun G K₂) = B then 1 else 0)
        * weight G β J (ofEdgeFun G m))]
  
  
  rw [show (∑ SS ∈ (univ : Finset (Finset (Copy G m) × Finset (Copy G m))).filter
              (fun SS => Disjoint SS.1 SS.2),
            ((if sources G (ofEdgeFun G (profileFlux G m SS.1)) = A then (1 : ℝ) else 0)
              * (if sources G (ofEdgeFun G (profileFlux G m SS.2)) = B then 1 else 0)
              * weight G β J (ofEdgeFun G m)))
        = (∑ SS ∈ (univ : Finset (Finset (Copy G m) × Finset (Copy G m))).filter
              (fun SS => Disjoint SS.1 SS.2),
            (if sources G (ofEdgeFun G (profileFlux G m SS.1)) = A
                ∧ sources G (ofEdgeFun G (profileFlux G m SS.2)) = B then (1 : ℝ) else 0))
          * weight G β J (ofEdgeFun G m) from ?_]
  · rw [Finset.sum_boole, Finset.filter_filter]
    congr 1
    rw [Nat.cast_inj]
    congr 1
    ext ⟨S₁, S₂⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset, Finset.subset_univ,
      mem_univ, true_and, sources_eq]
    try tauto
  · rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun SS _ => ?_)
    by_cases hA : sources G (ofEdgeFun G (profileFlux G m SS.1)) = A <;>
      by_cases hB : sources G (ofEdgeFun G (profileFlux G m SS.2)) = B <;>
      simp [hA, hB]


end StatMech.Walls

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MultiReplica.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.ClaimIsing.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.Switching.Part3
import Def.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
open Finset BigOperators SimpleGraph
open scoped symmDiff

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000


namespace StatMech

namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem sourceTripleSum_eq_mul (β : ℝ) (J : Sym2 V → ℝ) (A B C : Finset V) :
    sourceTripleSum G β J A B C
      = currentSum G β J A * currentSum G β J B * currentSum G β J C := by
  set f : (↥G.edgeFinset → ℕ) → ℝ :=
    fun p => if sources G (ofEdgeFun G p) = A then weight G β J (ofEdgeFun G p) else 0 with hf
  set g : (↥G.edgeFinset → ℕ) → ℝ :=
    fun p => if sources G (ofEdgeFun G p) = B then weight G β J (ofEdgeFun G p) else 0 with hg
  set k : (↥G.edgeFinset → ℕ) → ℝ :=
    fun p => if sources G (ofEdgeFun G p) = C then weight G β J (ofEdgeFun G p) else 0 with hk
  have hsumf : Summable f := (summable_norm_currentSum_summand G β J A).of_norm
  have hsumg : Summable g := (summable_norm_currentSum_summand G β J B).of_norm
  have hsumk : Summable k := (summable_norm_currentSum_summand G β J C).of_norm
  have hgknorm : Summable (fun w : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) => ‖g w.1 * k w.2‖) := by
    apply ((summable_norm_currentSum_summand G β J B).mul_of_nonneg
      (summable_norm_currentSum_summand G β J C)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).congr
    intro w; rw [norm_mul]
  have hgk : Summable (fun w : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) => g w.1 * k w.2) :=
    summable_mul_of_summable_norm (summable_norm_currentSum_summand G β J B)
      (summable_norm_currentSum_summand G β J C)
  have hABC := summable_mul_of_summable_norm (summable_norm_currentSum_summand G β J A) hgknorm
  
  show (∑' z : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
      f z.1 * g z.2.1 * k z.2.2)
      = (∑' p, f p) * (∑' p, g p) * (∑' p, k p)
  rw [show (fun z : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) =>
        f z.1 * g z.2.1 * k z.2.2)
      = fun z => f z.1 * (g z.2.1 * k z.2.2) from by funext z; rw [mul_assoc]]
  rw [← Summable.tsum_mul_tsum hsumf hgk hABC, ← Summable.tsum_mul_tsum hsumg hsumk hgk,
    mul_assoc]


theorem sourceTripleSum_eq_superposition (β : ℝ) (J : Sym2 V → ℝ) (A B C : Finset V) :
    sourceTripleSum G β J A B C
      = ∑' m : ↥G.edgeFinset → ℕ,
          ∑ K : {pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e},
            (if sources G (ofEdgeFun G K.1.1) = A then weight G β J (ofEdgeFun G K.1.1) else 0)
            * (if sources G (ofEdgeFun G K.1.2) = B then weight G β J (ofEdgeFun G K.1.2) else 0)
            * (if sources G (ofEdgeFun G (fun e => m e - K.1.1 e - K.1.2 e)) = C
                  then weight G β J (ofEdgeFun G (fun e => m e - K.1.1 e - K.1.2 e)) else 0) := by
  set f : (↥G.edgeFinset → ℕ) → ℝ :=
    fun p => if sources G (ofEdgeFun G p) = A then weight G β J (ofEdgeFun G p) else 0 with hf
  set g : (↥G.edgeFinset → ℕ) → ℝ :=
    fun p => if sources G (ofEdgeFun G p) = B then weight G β J (ofEdgeFun G p) else 0 with hg
  set k : (↥G.edgeFinset → ℕ) → ℝ :=
    fun p => if sources G (ofEdgeFun G p) = C then weight G β J (ofEdgeFun G p) else 0 with hk
  set F : (Σ m : (↥G.edgeFinset → ℕ),
      {pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e}) → ℝ :=
    fun s => f s.2.1.1 * g s.2.1.2 * k (fun e => s.1 e - s.2.1.1 e - s.2.1.2 e) with hF
  have hgknorm : Summable (fun w : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) => ‖g w.1 * k w.2‖) := by
    apply ((summable_norm_currentSum_summand G β J B).mul_of_nonneg
      (summable_norm_currentSum_summand G β J C)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).congr
    intro w; rw [norm_mul]
  have hABC := summable_mul_of_summable_norm (summable_norm_currentSum_summand G β J A) hgknorm
  have htriple : Summable (fun z : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) =>
      f z.1 * g z.2.1 * k z.2.2) := by
    have heq : (fun z : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) =>
        f z.1 * g z.2.1 * k z.2.2)
        = (fun z : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) =>
        f z.1 * (g z.2.1 * k z.2.2)) := by funext z; rw [mul_assoc]
    rw [heq]; exact hABC
  have hcomp : ∀ z : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
      f z.1 * g z.2.1 * k z.2.2 = F (tripleEquivSigma z) := by
    rintro ⟨p, q, r⟩
    simp only [hF, tripleEquivSigma, Equiv.coe_fn_mk]
    have hsub : (fun e => p e + q e + r e - p e - q e) = r := by ext e; omega
    rw [hsub]
  have hsumF : Summable F := by
    rw [← (tripleEquivSigma (E := ↥G.edgeFinset)).summable_iff]
    exact htriple.congr (fun z => hcomp z)
  unfold sourceTripleSum
  rw [tsum_congr hcomp, (tripleEquivSigma (E := ↥G.edgeFinset)).tsum_eq F,
    Summable.tsum_sigma hsumF]
  refine tsum_congr (fun m => ?_)
  rw [tsum_fintype]


theorem sourceTripleSum_superposition_source (m K₁ K₂ : ↥G.edgeFinset → ℕ)
    (hK : ∀ e, K₁ e + K₂ e ≤ m e) {A B C : Finset V}
    (hA : sources G (ofEdgeFun G K₁) = A) (hB : sources G (ofEdgeFun G K₂) = B)
    (hC : sources G (ofEdgeFun G (fun e => m e - K₁ e - K₂ e)) = C) :
    sources G (ofEdgeFun G m) = A ∆ B ∆ C := by
  rw [sources_ofEdgeFun_add₃ G m K₁ K₂ hK, hA, hB, hC]


theorem weight_split₃_eq_binom (β : ℝ) (J : Sym2 V → ℝ)
    (m K₁ K₂ : ↥G.edgeFinset → ℕ) (hK : ∀ e, K₁ e + K₂ e ≤ m e) :
    weight G β J (ofEdgeFun G K₁) * weight G β J (ofEdgeFun G K₂)
        * weight G β J (ofEdgeFun G (fun e => m e - K₁ e - K₂ e))
      = (∏ e ∈ G.edgeFinset,
          ((Nat.choose ((ofEdgeFun G m) e) ((ofEdgeFun G K₁) e) : ℝ)
            * (Nat.choose ((ofEdgeFun G m) e - (ofEdgeFun G K₁) e) ((ofEdgeFun G K₂) e) : ℝ)))
        * weight G β J (ofEdgeFun G m) := by
  have hsplit : ofEdgeFun G m
      = fun e => (ofEdgeFun G K₁) e + (ofEdgeFun G K₂) e
          + (ofEdgeFun G (fun e => m e - K₁ e - K₂ e)) e := by
    rw [ofEdgeFun_add₃]
    congr 1
    ext i
    have := hK i
    omega
  rw [weight_mul₃_eq G β J (ofEdgeFun G K₁) (ofEdgeFun G K₂)
    (ofEdgeFun G (fun e => m e - K₁ e - K₂ e))]
  congr 1
  · refine Finset.prod_congr rfl (fun e he => ?_)
    have hm1 : (ofEdgeFun G m) e
        = (ofEdgeFun G K₁) e + (ofEdgeFun G K₂) e
            + (ofEdgeFun G (fun e => m e - K₁ e - K₂ e)) e := by rw [hsplit]
    have hsub : (ofEdgeFun G m) e - (ofEdgeFun G K₁) e
        = (ofEdgeFun G K₂) e + (ofEdgeFun G (fun e => m e - K₁ e - K₂ e)) e := by
      rw [hm1]; omega
    rw [hsub, ← hm1]
  · rw [← hsplit]


namespace RandomCurrent

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

variable {W : Type*} [DecidableEq W] [Fintype W]


theorem sources_shift₂_bijOn (ends : ι → Sym2 W) (m P Q : Finset ι)
    (hP : P ⊆ m) (hQ : Q ⊆ m) (A : Finset W) :
    Set.BijOn (fun K => (K ∆ P) ∆ Q)
      {K | K ⊆ m ∧ sources ends K = A}
      {K | K ⊆ m ∧ sources ends K = A ∆ sources ends P ∆ sources ends Q} :=
  (sources_shift_bijOn ends m Q hQ (A ∆ sources ends P)).comp
    (sources_shift_bijOn ends m P hP A)


theorem switching_card₂ (ends : ι → Sym2 W) (m : Finset ι)
    (A : Finset W) {u v s t : W} (huv : u ≠ v) (hst : s ≠ t)
    (hconnuv : connK ends m u v) (hconnst : connK ends m s t) :
    #(m.powerset.filter (fun K => sources ends K = A ∆ {u, v} ∆ {s, t}))
      = #(m.powerset.filter (fun K => sources ends K = A)) := by
  obtain ⟨P, hPm, hPsrc⟩ := exists_conn_set ends m hconnuv huv
  obtain ⟨Q, hQm, hQsrc⟩ := exists_conn_set ends m hconnst hst
  have hbij := sources_shift₂_bijOn ends m P Q hPm hQm A
  rw [hPsrc, hQsrc] at hbij
  have himg : (m.powerset.filter (fun K => sources ends K = A ∆ {u, v} ∆ {s, t}))
      = (m.powerset.filter (fun K => sources ends K = A)).image (fun K => (K ∆ P) ∆ Q) := by
    ext K
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
    constructor
    · intro ⟨hKm, hKsrc⟩
      obtain ⟨L, hL, hLK⟩ := hbij.2.2 ⟨hKm, hKsrc⟩
      exact ⟨L, ⟨hL.1, hL.2⟩, hLK⟩
    · rintro ⟨L, ⟨hLm, hLsrc⟩, rfl⟩
      have := hbij.1 ⟨hLm, hLsrc⟩
      exact ⟨this.1, this.2⟩
  rw [himg, Finset.card_image_of_injOn]
  intro K₁ hK₁ K₂ hK₂ h
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hK₁ hK₂
  exact hbij.2.1 ⟨hK₁.1, hK₁.2⟩ ⟨hK₂.1, hK₂.2⟩ h


theorem switching_lemma₂ (ends : ι → Sym2 W) (m : Finset ι)
    (A : Finset W) {u v s t : W} (huv : u ≠ v) (hst : s ≠ t)
    (hconnuv : connK ends m u v) (hconnst : connK ends m s t) (F : Finset ι → ℝ) :
    ∑ _K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {u, v} ∆ {s, t}), F m
      = ∑ _K ∈ m.powerset.filter (fun K => sources ends K = A), F m := by
  rw [Finset.sum_const, Finset.sum_const, switching_card₂ ends m A huv hst hconnuv hconnst]

end RandomCurrent
end Sharpness
end StatMech

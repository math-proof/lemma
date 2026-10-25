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
import Def.StatisticalMechanics.Code.Sharpness.ClaimIsingFull.Part3
open SimpleGraph Finset
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000


namespace StatMech

namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem norm_factorSummand_le (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (A : Finset V)
    (a : {i : ↥G.edgeFinset // isIn G S i} → ℕ) :
    ‖factorSummand G β J S A a‖ ≤ ‖weight G β J (ofEdgeFun G (aFull G S a))‖ := by
  unfold factorSummand
  by_cases h : sources G (ofEdgeFun G (aFull G S a)) = A
  · rw [if_pos h]
  · rw [if_neg h, norm_zero]; positivity


theorem summable_factorSummand (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (A : Finset V) :
    Summable (factorSummand G β J S A) :=
  Summable.of_norm ((summable_norm_weight_aFull G β J S).of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_factorSummand_le G β J S A))


theorem norm_triple_le (w₁ w₂ : ℝ) (P₁ P₂ P₃ : Prop) [Decidable P₁] [Decidable P₂] [Decidable P₃] :
    ‖(if P₁ then w₁ else 0) * (if P₂ then w₂ else 0) * (if P₃ then (1 : ℝ) else 0)‖
      ≤ ‖w₁‖ * ‖w₂‖ := by
  rw [norm_mul, norm_mul]
  have h1 : ‖(if P₁ then w₁ else 0)‖ ≤ ‖w₁‖ := by by_cases h : P₁ <;> simp [h]
  have h2 : ‖(if P₂ then w₂ else 0)‖ ≤ ‖w₂‖ := by by_cases h : P₂ <;> simp [h]
  have h3 : ‖(if P₃ then (1 : ℝ) else 0)‖ ≤ 1 := by by_cases h : P₃ <;> simp [h]
  calc ‖if P₁ then w₁ else 0‖ * ‖if P₂ then w₂ else 0‖ * ‖if P₃ then (1 : ℝ) else 0‖
      ≤ ‖w₁‖ * ‖w₂‖ * 1 :=
        mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)) h3 (norm_nonneg _) (by positivity)
    _ = ‖w₁‖ * ‖w₂‖ := by ring


theorem norm_contextSummand_le (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (P : Current V → Prop)
    [DecidablePred P]
    (bn : ({i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ) × (↥G.edgeFinset → ℕ)) :
    ‖contextSummand G β J S P bn‖
      ≤ ‖weight G β J (ofEdgeFun G (bFull G S bn.1))‖ * ‖weight G β J (ofEdgeFun G bn.2)‖ :=
  norm_triple_le _ _ _ _ _


theorem summable_contextSummand (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (P : Current V → Prop)
    [DecidablePred P] :
    Summable (contextSummand G β J S P) := by
  have hdom : Summable (fun bn : ({i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ) × (↥G.edgeFinset → ℕ) =>
      ‖weight G β J (ofEdgeFun G (bFull G S bn.1))‖ * ‖weight G β J (ofEdgeFun G bn.2)‖) :=
    Summable.mul_of_nonneg (summable_norm_weight_bFull G β J S)
      (summable_norm_weight_ofEdgeFun G β J) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  exact Summable.of_norm (hdom.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_contextSummand_le G β J S P))


theorem summable_factor_context (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (A : Finset V)
    (P : Current V → Prop) [DecidablePred P] :
    Summable (fun abn : ({i : ↥G.edgeFinset // isIn G S i} → ℕ) ×
        (({i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ) × (↥G.edgeFinset → ℕ)) =>
      factorSummand G β J S A abn.1 * contextSummand G β J S P abn.2) := by
  have hfn : Summable (fun a => ‖factorSummand G β J S A a‖) :=
    (summable_norm_weight_aFull G β J S).of_nonneg_of_le (fun _ => norm_nonneg _)
      (norm_factorSummand_le G β J S A)
  have hgn : Summable (fun bn => ‖contextSummand G β J S P bn‖) := by
    have hdom : Summable (fun bn : ({i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ) × (↥G.edgeFinset → ℕ) =>
        ‖weight G β J (ofEdgeFun G (bFull G S bn.1))‖ * ‖weight G β J (ofEdgeFun G bn.2)‖) :=
      Summable.mul_of_nonneg (summable_norm_weight_bFull G β J S)
        (summable_norm_weight_ofEdgeFun G β J) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    exact hdom.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_contextSummand_le G β J S P)
  exact summable_mul_of_summable_norm hfn hgn


theorem claim2_pairSum_factor (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (P : Current V → Prop)
    [DecidablePred P]
    (H1 : ∀ m, P m → NoCrossing G m S)
    (H2 : ∀ m m' : Current V, (∀ i ∈ G.edgeFinset, ¬ edgeInside S i → m i = m' i) → (P m ↔ P m'))
    (A : Finset V) (hAS : A ⊆ S) :
    (∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
        (if sources G (ofEdgeFun G pq.1) = A then weight G β J (ofEdgeFun G pq.1) else 0)
          * (if sources G (ofEdgeFun G pq.2) = ∅ then weight G β J (ofEdgeFun G pq.2) else 0)
          * (if P (fun e => ofEdgeFun G pq.1 e + ofEdgeFun G pq.2 e) then 1 else 0))
    = currentSum G β (couplingIn J S) A
      * (∑' bn : ({i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ) × (↥G.edgeFinset → ℕ),
          contextSummand G β J S P bn) := by
  
  set E := Equiv.piEquivPiSubtypeProd (isIn G S) (fun _ : ↥G.edgeFinset => ℕ)
  set E' := E.prodCongr (Equiv.refl (↥G.edgeFinset → ℕ))
  
  rw [← E'.symm.tsum_eq]
  
  have hsummand : ∀ pq : (({i : ↥G.edgeFinset // isIn G S i} → ℕ)
        × ({i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ)) × (↥G.edgeFinset → ℕ),
      ((if sources G (ofEdgeFun G (E'.symm pq).1) = A then weight G β J (ofEdgeFun G (E'.symm pq).1) else 0)
          * (if sources G (ofEdgeFun G (E'.symm pq).2) = ∅ then weight G β J (ofEdgeFun G (E'.symm pq).2) else 0)
          * (if P (fun e => ofEdgeFun G (E'.symm pq).1 e + ofEdgeFun G (E'.symm pq).2 e) then 1 else 0))
        = factorSummand G β J S A pq.1.1 * contextSummand G β J S P (pq.1.2, pq.2) := by
    rintro ⟨⟨a, b⟩, n₂⟩
    have heq : E'.symm ((a, b), n₂) = (reEdge G S (a, b), n₂) := rfl
    rw [heq]
    unfold factorSummand contextSummand
    exact summand_factor G β J S P H1 H2 A hAS a b n₂
  rw [tsum_congr hsummand]
  
  rw [show (∑' pq : (({i : ↥G.edgeFinset // isIn G S i} → ℕ)
            × ({i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ)) × (↥G.edgeFinset → ℕ),
          factorSummand G β J S A pq.1.1 * contextSummand G β J S P (pq.1.2, pq.2))
        = ∑' pq, (fun abn => factorSummand G β J S A abn.1 * contextSummand G β J S P abn.2)
            (Equiv.prodAssoc _ _ _ pq) from rfl]
  rw [(Equiv.prodAssoc _ _ _).tsum_eq (fun abn => factorSummand G β J S A abn.1
      * contextSummand G β J S P abn.2)]
  rw [← Summable.tsum_mul_tsum (summable_factorSummand G β J S A) (summable_contextSummand G β J S P)
      (summable_factor_context G β J S A P)]
  rw [currentSum_couplingIn_eq]
  rfl


theorem claim2_abstract (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (P : Current V → Prop)
    [DecidablePred P]
    (H1 : ∀ m, P m → NoCrossing G m S)
    (H2 : ∀ m m' : Current V, (∀ i ∈ G.edgeFinset, ¬ edgeInside S i → m i = m' i) → (P m ↔ P m'))
    (zero x : V) (h0 : zero ∈ S) (hx : x ∈ S)
    (hZ : currentSum G β (couplingIn J S) ∅ ≠ 0) :
    (∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
        (if sources G (ofEdgeFun G pq.1) = {zero, x} then weight G β J (ofEdgeFun G pq.1) else 0)
          * (if sources G (ofEdgeFun G pq.2) = ∅ then weight G β J (ofEdgeFun G pq.2) else 0)
          * (if P (fun e => ofEdgeFun G pq.1 e + ofEdgeFun G pq.2 e) then 1 else 0))
    = expectationJ G β (couplingIn J S) {zero, x}
      * (∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
          (if sources G (ofEdgeFun G pq.1) = ∅ then weight G β J (ofEdgeFun G pq.1) else 0)
            * (if sources G (ofEdgeFun G pq.2) = ∅ then weight G β J (ofEdgeFun G pq.2) else 0)
            * (if P (fun e => ofEdgeFun G pq.1 e + ofEdgeFun G pq.2 e) then 1 else 0)) := by
  have h0x : ({zero, x} : Finset V) ⊆ S := by
    intro v hv; rw [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact h0
    · exact hx
  rw [claim2_pairSum_factor G β J S P H1 H2 {zero, x} h0x,
    claim2_pairSum_factor G β J S P H1 H2 ∅ (Finset.empty_subset _)]
  
  rw [current_representation]
  rw [div_mul_eq_mul_div, mul_div_assoc,
    mul_comm (currentSum G β (couplingIn J S) ∅), mul_div_assoc, div_self hZ, mul_one]


end Sharpness
end StatMech

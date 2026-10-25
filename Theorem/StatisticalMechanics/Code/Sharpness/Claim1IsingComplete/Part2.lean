/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Claim1IsingComplete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.Claim1IsingFull.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.ClaimIsingFull.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.Simon.Part3
import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
import Def.StatisticalMechanics.Code.Sharpness.Claim1IsingComplete
open SimpleGraph Finset
open scoped BigOperators symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000


namespace StatMech

namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem claim1_summand_factor (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V)
    (P : Current V → Prop) [DecidablePred P]
    (H1 : ∀ m, P m → NoCrossing G m S)
    (H2 : ∀ m m' : Current V,
      (∀ i ∈ G.edgeFinset, ¬ edgeInside S i → m i = m' i) → (P m ↔ P m'))
    (A B C D : Finset V) (hAS : A ⊆ S) (hBS : B ⊆ Sᶜ)
    (hCS : C ⊆ S) (hDS : D ⊆ Sᶜ)
    (a c : {i : ↥G.edgeFinset // isIn G S i} → ℕ)
    (b d : {i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ) :
    (if sources G (ofEdgeFun G (reEdge G S (a, b))) = A ∆ B
        then weight G β J (ofEdgeFun G (reEdge G S (a, b))) else 0) *
      (if sources G (ofEdgeFun G (reEdge G S (c, d))) = C ∆ D
        then weight G β J (ofEdgeFun G (reEdge G S (c, d))) else 0) *
      (if P (fun e => ofEdgeFun G (reEdge G S (a, b)) e +
          ofEdgeFun G (reEdge G S (c, d)) e) then 1 else 0)
    = factorSummand G β J S A a * factorSummand G β J S C c *
        claim1Context G β J S P B D (b, d) := by
  let m : Current V := fun e => ofEdgeFun G (reEdge G S (a, b)) e +
    ofEdgeFun G (reEdge G S (c, d)) e
  let m' : Current V := fun e => ofEdgeFun G (bFull G S b) e +
    ofEdgeFun G (bFull G S d) e
  have hP : P m ↔ P m' := by
    apply H2
    intro i _ hi
    have hab : ofEdgeFun G (reEdge G S (a, b)) i = ofEdgeFun G (bFull G S b) i := by
      unfold ofEdgeFun
      by_cases he : i ∈ G.edgeFinset
      · rw [dif_pos he, dif_pos he, reEdge_eq_add, aFull, dif_neg (by unfold isIn; exact hi), zero_add]
      · rw [dif_neg he, dif_neg he]
    have hcd : ofEdgeFun G (reEdge G S (c, d)) i = ofEdgeFun G (bFull G S d) i := by
      unfold ofEdgeFun
      by_cases he : i ∈ G.edgeFinset
      · rw [dif_pos he, dif_pos he, reEdge_eq_add, aFull, dif_neg (by unfold isIn; exact hi), zero_add]
      · rw [dif_neg he, dif_neg he]
    exact congrArg₂ (· + ·) hab hcd
  by_cases hev : P m'
  · have hnc : NoCrossing G m S := H1 m (hP.mpr hev)
    have hbCross : ∀ i : ↥G.edgeFinset, 1 ≤ bFull G S b i → edgeInside Sᶜ (i : Sym2 V) := by
      intro i hipos
      have hsuper : 1 ≤ m i.1 := by
        have hle : bFull G S b i ≤ ofEdgeFun G (reEdge G S (a, b)) i.1 := by
          rw [show ofEdgeFun G (reEdge G S (a, b)) i.1 = reEdge G S (a, b) i from by
            unfold ofEdgeFun; rw [dif_pos i.2], reEdge_eq_add]
          omega
        simp only [m]; omega
      rcases hnc i.1 i.2 hsuper with hi | hi
      · exfalso
        have hni : ¬ isIn G S i := by
          intro his
          unfold bFull at hipos
          rw [dif_pos his] at hipos
          omega
        exact hni hi
      · exact hi
    have hdCross : ∀ i : ↥G.edgeFinset, 1 ≤ bFull G S d i → edgeInside Sᶜ (i : Sym2 V) := by
      intro i hipos
      have hsuper : 1 ≤ m i.1 := by
        have hle : bFull G S d i ≤ ofEdgeFun G (reEdge G S (c, d)) i.1 := by
          rw [show ofEdgeFun G (reEdge G S (c, d)) i.1 = reEdge G S (c, d) i from by
            unfold ofEdgeFun; rw [dif_pos i.2], reEdge_eq_add]
          omega
        simp only [m]; omega
      rcases hnc i.1 i.2 hsuper with hi | hi
      · exfalso
        have hni : ¬ isIn G S i := by
          intro his
          unfold bFull at hipos
          rw [dif_pos his] at hipos
          omega
        exact hni hi
      · exact hi
    have hsrc1 := sources_reEdge_eq_symmDiff_iff G S A B hAS hBS a b hbCross
    have hsrc2 := sources_reEdge_eq_symmDiff_iff G S C D hCS hDS c d hdCross
    unfold factorSummand claim1Context
    change P (fun e => ofEdgeFun G (bFull G S b) e +
      ofEdgeFun G (bFull G S d) e) at hev
    have hevFull : P (fun e => ofEdgeFun G (reEdge G S (a, b)) e +
        ofEdgeFun G (reEdge G S (c, d)) e) := hP.mpr hev
    rw [if_pos hev, if_pos hevFull]
    simp only [weight_reEdge_split]
    by_cases ha : sources G (ofEdgeFun G (aFull G S a)) = A <;>
      by_cases hb : sources G (ofEdgeFun G (bFull G S b)) = B <;>
      by_cases hc : sources G (ofEdgeFun G (aFull G S c)) = C <;>
      by_cases hd : sources G (ofEdgeFun G (bFull G S d)) = D <;>
      simp [hsrc1, hsrc2, ha, hb, hc, hd] <;> ring
  · have hnfull : ¬ P m := fun h => hev (hP.mp h)
    unfold claim1Context
    change ¬ P (fun e => ofEdgeFun G (bFull G S b) e +
      ofEdgeFun G (bFull G S d) e) at hev
    change ¬ P (fun e => ofEdgeFun G (reEdge G S (a, b)) e +
      ofEdgeFun G (reEdge G S (c, d)) e) at hnfull
    rw [if_neg hev, if_neg hnfull]
    ring


theorem norm_claim1Context_le (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V)
    (P : Current V → Prop) [DecidablePred P] (B D : Finset V)
    (bd : ({i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ) ×
      ({i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ)) :
    ‖claim1Context G β J S P B D bd‖ ≤
      ‖weight G β J (ofEdgeFun G (bFull G S bd.1))‖ *
        ‖weight G β J (ofEdgeFun G (bFull G S bd.2))‖ :=
  norm_triple_le _ _ _ _ _

theorem summable_claim1Context (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V)
    (P : Current V → Prop) [DecidablePred P] (B D : Finset V) :
    Summable (claim1Context G β J S P B D) := by
  have hdom : Summable (fun bd :
      ({i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ) ×
      ({i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ) =>
      ‖weight G β J (ofEdgeFun G (bFull G S bd.1))‖ *
        ‖weight G β J (ofEdgeFun G (bFull G S bd.2))‖) :=
    Summable.mul_of_nonneg (summable_norm_weight_bFull G β J S)
      (summable_norm_weight_bFull G β J S) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  exact Summable.of_norm (hdom.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_claim1Context_le G β J S P B D))

theorem summable_claim1Interior (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V)
    (A C : Finset V) :
    Summable (fun ac :
      ({i : ↥G.edgeFinset // isIn G S i} → ℕ) ×
      ({i : ↥G.edgeFinset // isIn G S i} → ℕ) =>
      factorSummand G β J S A ac.1 * factorSummand G β J S C ac.2) :=
  summable_mul_of_summable_norm
    ((summable_factorSummand G β J S A).norm)
    ((summable_factorSummand G β J S C).norm)


theorem claim1_pairSum_factor (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V)
    (P : Current V → Prop) [DecidablePred P]
    (H1 : ∀ m, P m → NoCrossing G m S)
    (H2 : ∀ m m' : Current V,
      (∀ i ∈ G.edgeFinset, ¬ edgeInside S i → m i = m' i) → (P m ↔ P m'))
    (A B C D : Finset V) (hAS : A ⊆ S) (hBS : B ⊆ Sᶜ)
    (hCS : C ⊆ S) (hDS : D ⊆ Sᶜ) :
    (∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
      (if sources G (ofEdgeFun G pq.1) = A ∆ B then weight G β J (ofEdgeFun G pq.1) else 0) *
        (if sources G (ofEdgeFun G pq.2) = C ∆ D then weight G β J (ofEdgeFun G pq.2) else 0) *
        (if P (fun e => ofEdgeFun G pq.1 e + ofEdgeFun G pq.2 e) then 1 else 0))
    = currentSum G β (couplingIn J S) A * currentSum G β (couplingIn J S) C *
        (∑' bd, claim1Context G β J S P B D bd) := by
  let E := Equiv.piEquivPiSubtypeProd (isIn G S) (fun _ : ↥G.edgeFinset => ℕ)
  let E2 := E.prodCongr E
  rw [← E2.symm.tsum_eq]
  have hsummand : ∀ q,
      ((if sources G (ofEdgeFun G (E2.symm q).1) = A ∆ B
          then weight G β J (ofEdgeFun G (E2.symm q).1) else 0) *
        (if sources G (ofEdgeFun G (E2.symm q).2) = C ∆ D
          then weight G β J (ofEdgeFun G (E2.symm q).2) else 0) *
        (if P (fun e => ofEdgeFun G (E2.symm q).1 e + ofEdgeFun G (E2.symm q).2 e)
          then 1 else 0)) =
      factorSummand G β J S A q.1.1 * factorSummand G β J S C q.2.1 *
        claim1Context G β J S P B D (q.1.2, q.2.2) := by
    rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩
    exact claim1_summand_factor G β J S P H1 H2 A B C D hAS hBS hCS hDS a c b d
  rw [tsum_congr hsummand]
  have hgroup : ∀ q,
      factorSummand G β J S A q.1.1 * factorSummand G β J S C q.2.1 *
          claim1Context G β J S P B D (q.1.2, q.2.2) =
        (fun r =>
          (factorSummand G β J S A r.1.1 * factorSummand G β J S C r.1.2) *
            claim1Context G β J S P B D r.2) (pairCutEquiv G S q) := by
    rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩
    rfl
  rw [tsum_congr hgroup]
  rw [(pairCutEquiv G S).tsum_eq (fun r =>
    (factorSummand G β J S A r.1.1 * factorSummand G β J S C r.1.2) *
      claim1Context G β J S P B D r.2)]
  have hi := summable_claim1Interior G β J S A C
  have he := summable_claim1Context G β J S P B D
  have hie := summable_mul_of_summable_norm hi.norm he.norm
  rw [← Summable.tsum_mul_tsum hi he hie]
  rw [← Summable.tsum_mul_tsum (summable_factorSummand G β J S A)
    (summable_factorSummand G β J S C) (summable_claim1Interior G β J S A C)]
  rw [currentSum_couplingIn_eq, currentSum_couplingIn_eq]
  ac_rfl


end Sharpness
end StatMech

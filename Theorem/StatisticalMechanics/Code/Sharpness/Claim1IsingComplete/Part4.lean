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
import Def.StatisticalMechanics.Code.Sharpness.Claim1IsingComplete.Part3
open SimpleGraph Finset
open scoped BigOperators symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000


namespace StatMech

namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


open FluxEdgeCopy


theorem expectationJ_eq_expJ (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) :
    expectationJ G β J A =
      expJ G.edgeFinset (fun e => β * J e) (fun _ => 0) (Ising.spinProd A) := by
  have hw : ∀ s : ConfigSpace V,
      boltzmannJ G β J s = wJ G.edgeFinset (fun e => β * J e) (fun _ => 0) s := by
    intro s
    unfold boltzmannJ wJ
    congr 1
    simp only [zero_mul, Finset.sum_const_zero, add_zero, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring
  unfold expectationJ expJ partitionJ ZJ
  simp_rw [hw]


theorem expectationJ_couplingIn_eq_expJ (β : ℝ) (J : Sym2 V → ℝ)
    (S A : Finset V) :
    expectationJ G β (couplingIn J S) A =
      expJ (edgesIn G S) (fun e => β * J e) (fun _ => 0) (Ising.spinProd A) := by
  have hw : ∀ s : ConfigSpace V,
      boltzmannJ G β (couplingIn J S) s =
        wJ (edgesIn G S) (fun e => β * J e) (fun _ => 0) s := by
    intro s
    unfold boltzmannJ wJ couplingIn edgesIn
    congr 1
    simp only [zero_mul, Finset.sum_const_zero, add_zero, Finset.mul_sum]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hi : edgeInside S e <;> simp [hi] <;> ring
  unfold expectationJ expJ partitionJ ZJ
  simp_rw [hw]


theorem expectationJ_couplingIn_le (β : ℝ) (J : Sym2 V → ℝ)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e) (S A : Finset V) :
    expectationJ G β (couplingIn J S) A ≤ expectationJ G β J A := by
  rw [expectationJ_couplingIn_eq_expJ, expectationJ_eq_expJ]
  apply griffiths_mono (edgesIn G S) G.edgeFinset (fun e => β * J e) (fun _ => 0)
  · intro e he
    exact (Finset.mem_filter.mp he).1
  · intro e _
    exact mul_nonneg hβ (hJ e)
  · intro x
    exact le_rfl
  · intro e he _
    exact G.not_isDiag_of_mem_edgeFinset he


theorem gatedSourcePairSum_factor (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V)
    (P : Current V → Prop) [DecidablePred P]
    (H1 : ∀ m, P m → NoCrossing G m S)
    (H2 : ∀ m m' : Current V,
      (∀ i ∈ G.edgeFinset, ¬ edgeInside S i → m i = m' i) → (P m ↔ P m'))
    (A B C D : Finset V) (hAS : A ⊆ S) (hBS : B ⊆ Sᶜ)
    (hCS : C ⊆ S) (hDS : D ⊆ Sᶜ) :
    gatedSourcePairSum G β J (A ∆ B) (C ∆ D) P =
      currentSum G β (couplingIn J S) A * currentSum G β (couplingIn J S) C *
        (∑' bd, claim1Context G β J S P B D bd) := by
  unfold gatedSourcePairSum
  simpa only [ofEdgeFun_add] using
    claim1_pairSum_factor G β J S P H1 H2 A B C D hAS hBS hCS hDS


theorem claim1Context_nonneg (β : ℝ) (J : Sym2 V → ℝ)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e) (S : Finset V)
    (P : Current V → Prop) [DecidablePred P] (B D : Finset V) :
    0 ≤ ∑' bd, claim1Context G β J S P B D bd := by
  apply tsum_nonneg
  rintro ⟨b, d⟩
  unfold claim1Context
  by_cases hb : sources G (ofEdgeFun G (bFull G S b)) = B <;>
    by_cases hd : sources G (ofEdgeFun G (bFull G S d)) = D <;>
    by_cases hp : P (fun e => ofEdgeFun G (bFull G S b) e +
      ofEdgeFun G (bFull G S d) e) <;> simp [hb, hd, hp]
  exact mul_nonneg
    (Ising.acw_weight_nonneg G β J hβ hJ (ofEdgeFun G (bFull G S b)))
    (Ising.acw_weight_nonneg G β J hβ hJ (ofEdgeFun G (bFull G S d)))


theorem claim1_ising_cleared (β : ℝ) (J : Sym2 V → ℝ)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (S : Finset V) (o x y g : V)
    (ho : o ∉ S) (hx : x ∉ S) (hy : y ∈ S) (hg : g ∈ S)
    (hyg : y ≠ g) (mΛ : ℝ)
    (hgriff : expectationJ G β (couplingIn J S) {y, g} ≤ mΛ) :
    mΛ * gatedSourcePairSum G β J (({y, g} : Finset V) ∆ {o, x}) ∅
        (fun m => notConnComp G m o = S) ≥
      gatedSourcePairSum G β J {o, x} ∅
        (fun m => notConnComp G m o = S ∧ CurrentConnected G m y g) := by
  let P : Current V → Prop := fun m => notConnComp G m o = S
  have H1 : ∀ m, P m → NoCrossing G m S := fun m hm =>
    noCrossing_of_event G m S o ho hm
  have H2 : ∀ m m' : Current V,
      (∀ i ∈ G.edgeFinset, ¬ edgeInside S i → m i = m' i) → (P m ↔ P m') := by
    intro m m' heq
    constructor
    · intro hm
      exact notConnComp_congr G m m' S o ho hm heq
    · intro hm'
      exact notConnComp_congr G m' m S o ho hm' (fun i hi hni => (heq i hi hni).symm)
  have hA : ({y, g} : Finset V) ⊆ S := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  have hB : ({o, x} : Finset V) ⊆ Sᶜ := by
    intro z hz
    rw [Finset.mem_compl]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  have hE : (∅ : Finset V) ⊆ S := Finset.empty_subset _
  have hEc : (∅ : Finset V) ⊆ Sᶜ := Finset.empty_subset _
  let cA := currentSum G β (couplingIn J S) ({y, g} : Finset V)
  let c0 := currentSum G β (couplingIn J S) ∅
  let C := ∑' bd, claim1Context G β J S P ({o, x} : Finset V) ∅ bd
  have hcA : cA = expectationJ G β (couplingIn J S) {y, g} * c0 := by
    exact Ising.acr_eq15_insertion' G β (couplingIn J S) {y, g}
  have heS : 0 ≤ expectationJ G β (couplingIn J S) {y, g} :=
    Ising.acr_expectationJ_nonneg G β (couplingIn J S) hβ
      (fun e => by unfold couplingIn; split <;> simp_all [hJ e]) {y, g}
  have hc0 : 0 ≤ c0 :=
    Ising.acr_currentSum_nonneg G β (couplingIn J S) hβ
      (fun e => by unfold couplingIn; split <;> simp_all [hJ e]) ∅
  have hlocal : mΛ * cA * c0 ≥ cA * cA := by
    rw [hcA]
    have hm := mul_le_mul_of_nonneg_right hgriff (mul_nonneg heS (sq_nonneg c0))
    nlinarith
  have hC : 0 ≤ C := claim1Context_nonneg G β J hβ hJ S P {o, x} ∅
  have htheta := gatedSourcePairSum_factor G β J S P H1 H2
    ({y, g} : Finset V) {o, x} ∅ ∅ hA hB hE hEc
  have hpre := gatedSourcePairSum_factor G β J S P H1 H2
    ({y, g} : Finset V) {o, x} {y, g} ∅ hA hB hA hEc
  have hee : (∅ : Finset V) ∆ ∅ = ∅ := by ext z; simp [Finset.mem_symmDiff]
  have ha0 : ({y, g} : Finset V) ∆ ∅ = {y, g} := by
    ext z; simp [Finset.mem_symmDiff]
  rw [hee] at htheta
  rw [ha0] at hpre
  have hmul := mul_le_mul_of_nonneg_right hlocal hC
  have hswitch := gatedSourcePairSum_switching G β J ({o, x} : Finset V) hyg P
  change mΛ * gatedSourcePairSum G β J (({y, g} : Finset V) ∆ {o, x}) ∅ P ≥ _
  rw [htheta]
  rw [← hswitch]
  rw [show ({o, x} : Finset V) ∆ {y, g} = {y, g} ∆ {o, x} by
    apply symmDiff_comm]
  rw [hpre]
  nlinarith


theorem claim1_ising (β : ℝ) (J : Sym2 V → ℝ)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (S : Finset V) (o x y g : V)
    (ho : o ∉ S) (hx : x ∉ S) (hy : y ∈ S) (hg : g ∈ S)
    (hyg : y ≠ g) (mΛ : ℝ) (hmΛ : 0 < mΛ)
    (hgriff : expectationJ G β (couplingIn J S) {y, g} ≤ mΛ) :
    gatedSourcePairSum G β J (({y, g} : Finset V) ∆ {o, x}) ∅
        (fun m => notConnComp G m o = S) ≥
      mΛ⁻¹ * gatedSourcePairSum G β J {o, x} ∅
        (fun m => notConnComp G m o = S ∧ CurrentConnected G m y g) := by
  have h := claim1_ising_cleared G β J hβ hJ S o x y g ho hx hy hg hyg mΛ hgriff
  have hm := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hmΛ.le)
  calc
    mΛ⁻¹ * gatedSourcePairSum G β J {o, x} ∅
        (fun m => notConnComp G m o = S ∧ CurrentConnected G m y g)
      ≤ mΛ⁻¹ * (mΛ * gatedSourcePairSum G β J (({y, g} : Finset V) ∆ {o, x}) ∅
          (fun m => notConnComp G m o = S)) := hm
    _ = gatedSourcePairSum G β J (({y, g} : Finset V) ∆ {o, x}) ∅
          (fun m => notConnComp G m o = S) := by
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hmΛ), one_mul]


theorem claim1_ising_unconditional_cleared (β : ℝ) (J : Sym2 V → ℝ)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (S : Finset V) (o x y g : V)
    (ho : o ∉ S) (hx : x ∉ S) (hy : y ∈ S) (hg : g ∈ S)
    (hyg : y ≠ g) :
    expectationJ G β J {y, g} *
        gatedSourcePairSum G β J (({y, g} : Finset V) ∆ {o, x}) ∅
          (fun m => notConnComp G m o = S) ≥
      gatedSourcePairSum G β J {o, x} ∅
        (fun m => notConnComp G m o = S ∧ CurrentConnected G m y g) :=
  claim1_ising_cleared G β J hβ hJ S o x y g ho hx hy hg hyg
    (expectationJ G β J {y, g})
    (expectationJ_couplingIn_le G β J hβ hJ S {y, g})


theorem claim1_ising_self_cleared (β : ℝ) (J : Sym2 V → ℝ)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (S : Finset V) (o y g : V)
    (ho : o ∉ S) (hy : y ∈ S) (hg : g ∈ S) (hyg : y ≠ g) :
    expectationJ G β J {y, g} *
        gatedSourcePairSum G β J {y, g} ∅
          (fun m => notConnComp G m o = S) ≥
      gatedSourcePairSum G β J ∅ ∅
        (fun m => notConnComp G m o = S ∧ CurrentConnected G m y g) := by
  let P : Current V → Prop := fun m => notConnComp G m o = S
  have H1 : ∀ m, P m → NoCrossing G m S := fun m hm =>
    noCrossing_of_event G m S o ho hm
  have H2 : ∀ m m' : Current V,
      (∀ i ∈ G.edgeFinset, ¬ edgeInside S i → m i = m' i) → (P m ↔ P m') := by
    intro m m' heq
    constructor
    · intro hm
      exact notConnComp_congr G m m' S o ho hm heq
    · intro hm'
      exact notConnComp_congr G m' m S o ho hm'
        (fun i hi hni => (heq i hi hni).symm)
  have hA : ({y, g} : Finset V) ⊆ S := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  have hE : (∅ : Finset V) ⊆ S := Finset.empty_subset _
  have hEc : (∅ : Finset V) ⊆ Sᶜ := Finset.empty_subset _
  let cA := currentSum G β (couplingIn J S) ({y, g} : Finset V)
  let c0 := currentSum G β (couplingIn J S) ∅
  let C := ∑' bd, claim1Context G β J S P ∅ ∅ bd
  have hcA : cA = expectationJ G β (couplingIn J S) {y, g} * c0 :=
    Ising.acr_eq15_insertion' G β (couplingIn J S) {y, g}
  have heS : 0 ≤ expectationJ G β (couplingIn J S) {y, g} :=
    Ising.acr_expectationJ_nonneg G β (couplingIn J S) hβ
      (fun e => by unfold couplingIn; split <;> simp_all [hJ e]) {y, g}
  have hc0 : 0 ≤ c0 :=
    Ising.acr_currentSum_nonneg G β (couplingIn J S) hβ
      (fun e => by unfold couplingIn; split <;> simp_all [hJ e]) ∅
  have hgriff := expectationJ_couplingIn_le G β J hβ hJ S {y, g}
  have hlocal : expectationJ G β J {y, g} * cA * c0 ≥ cA * cA := by
    rw [hcA]
    have hm := mul_le_mul_of_nonneg_right hgriff (mul_nonneg heS (sq_nonneg c0))
    calc
      (expectationJ G β (couplingIn J S) {y, g} * c0) *
          (expectationJ G β (couplingIn J S) {y, g} * c0) =
          expectationJ G β (couplingIn J S) {y, g} *
            (expectationJ G β (couplingIn J S) {y, g} * c0 ^ 2) := by ring
      _ ≤ expectationJ G β J {y, g} *
            (expectationJ G β (couplingIn J S) {y, g} * c0 ^ 2) := hm
      _ = expectationJ G β J {y, g} *
            (expectationJ G β (couplingIn J S) {y, g} * c0) * c0 := by ring
  have hC : 0 ≤ C := claim1Context_nonneg G β J hβ hJ S P ∅ ∅
  have htheta := gatedSourcePairSum_factor G β J S P H1 H2
    ({y, g} : Finset V) ∅ ∅ ∅ hA hEc hE hEc
  have hpre := gatedSourcePairSum_factor G β J S P H1 H2
    ({y, g} : Finset V) ∅ ({y, g} : Finset V) ∅ hA hEc hA hEc
  have hee : (∅ : Finset V) ∆ ∅ = ∅ := by ext z; simp [Finset.mem_symmDiff]
  have ha0 : ({y, g} : Finset V) ∆ ∅ = {y, g} := by
    ext z; simp [Finset.mem_symmDiff]
  have h0a : (∅ : Finset V) ∆ {y, g} = {y, g} := by
    ext z; simp [Finset.mem_symmDiff]
  rw [hee] at htheta
  rw [ha0] at htheta
  rw [ha0] at hpre
  have hmul := mul_le_mul_of_nonneg_right hlocal hC
  have hswitch := gatedSourcePairSum_switching G β J (∅ : Finset V) hyg P
  rw [h0a] at hswitch
  change expectationJ G β J {y, g} *
      gatedSourcePairSum G β J {y, g} ∅ P ≥ _
  rw [htheta]
  rw [← hswitch]
  rw [hpre]
  simpa only [mul_assoc] using hmul


theorem claim1_ising_unconditional (β : ℝ) (J : Sym2 V → ℝ)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (S : Finset V) (o x y g : V)
    (ho : o ∉ S) (hx : x ∉ S) (hy : y ∈ S) (hg : g ∈ S)
    (hyg : y ≠ g) (hm : 0 < expectationJ G β J {y, g}) :
    gatedSourcePairSum G β J (({y, g} : Finset V) ∆ {o, x}) ∅
        (fun m => notConnComp G m o = S) ≥
      (expectationJ G β J {y, g})⁻¹ * gatedSourcePairSum G β J {o, x} ∅
        (fun m => notConnComp G m o = S ∧ CurrentConnected G m y g) :=
  claim1_ising G β J hβ hJ S o x y g ho hx hy hg hyg
    (expectationJ G β J {y, g}) hm
    (expectationJ_couplingIn_le G β J hβ hJ S {y, g})

end Sharpness
end StatMech

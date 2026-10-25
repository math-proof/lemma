/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part13
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem summable_natSucc_mul_norm_wEdge
    {V : Type*}
    (β : ℝ) (J : Sym2 V → ℝ) (e : Sym2 V) :
    Summable (fun k : ℕ =>
      (((k + 1 : ℕ) : ℝ) * ‖Sharpness.wEdge β J e k‖)) := by
  let x : ℝ := |β * J e|
  have hdom : ∀ k : ℕ,
      (((k + 1 : ℕ) : ℝ) * ‖Sharpness.wEdge β J e k‖) ≤
        (2 * x) ^ k / (Nat.factorial k : ℝ) := by
    intro k
    have hcast : (((k + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ k) := by
      exact_mod_cast nat_succ_le_two_pow k
    have hxpow : 0 ≤ x ^ k := pow_nonneg (abs_nonneg _) k
    have hnum :
        (((k + 1 : ℕ) : ℝ) * x ^ k) ≤ (2 : ℝ) ^ k * x ^ k :=
      mul_le_mul_of_nonneg_right hcast hxpow
    have hfacnonneg : 0 ≤ (Nat.factorial k : ℝ) := by positivity
    calc
      (((k + 1 : ℕ) : ℝ) * ‖Sharpness.wEdge β J e k‖)
          = (((k + 1 : ℕ) : ℝ) *
              (x ^ k / (Nat.factorial k : ℝ))) := by
            dsimp [Sharpness.wEdge, x]
            rw [abs_div, abs_pow]
            simp [abs_of_nonneg
              (by positivity : 0 ≤ (Nat.factorial k : ℝ))]
      _ = (((k + 1 : ℕ) : ℝ) * x ^ k) /
          (Nat.factorial k : ℝ) := by ring
      _ ≤ ((2 : ℝ) ^ k * x ^ k) / (Nat.factorial k : ℝ) :=
        div_le_div_of_nonneg_right hnum hfacnonneg
      _ = (2 * x) ^ k / (Nat.factorial k : ℝ) := by rw [mul_pow]
  have hnonneg : ∀ k : ℕ,
      0 ≤ (((k + 1 : ℕ) : ℝ) * ‖Sharpness.wEdge β J e k‖) := by
    intro k
    exact mul_nonneg (by positivity) (norm_nonneg _)
  have hsumdom :
      Summable (fun k : ℕ => (2 * x) ^ k / (Nat.factorial k : ℝ)) := by
    have h := NormedSpace.expSeries_summable' (𝕂 := ℝ) (2 * x)
    convert h using 2 with k
    rw [smul_eq_mul, div_eq_inv_mul]
  exact Summable.of_nonneg_of_le hnonneg hdom hsumdom

set_option linter.style.longLine false in


theorem summable_edgeMultiplicitySucc_mul_norm_weight_ofEdgeFun
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ)
    (e0 : ↥G.edgeFinset) :
    Summable (fun m : ↥G.edgeFinset → ℕ =>
      (((m e0 + 1 : ℕ) : ℝ) *
        ‖Sharpness.weight G β J (Sharpness.ofEdgeFun G m)‖)) := by
  classical
  let g : Sym2 V → ℕ → ℝ := fun e k =>
    if e = e0.1 then
      (((k + 1 : ℕ) : ℝ) * ‖Sharpness.wEdge β J e k‖)
    else
      ‖Sharpness.wEdge β J e k‖
  have hg : ∀ e : Sym2 V, Summable (g e) := by
    intro e
    by_cases he : e = e0.1
    · simpa [g, he] using summable_natSucc_mul_norm_wEdge (β := β) (J := J) e
    · simpa [g, he] using Sharpness.summable_norm_wEdge (β := β) (J := J) e
  have hgnn : ∀ e : Sym2 V, ∀ k : ℕ, 0 ≤ g e k := by
    intro e k
    by_cases he : e = e0.1
    · subst he
      dsimp [g]
      rw [if_pos rfl]
      exact mul_nonneg (by positivity) (abs_nonneg _)
    · simp [g, he]
  have hprod := (Sharpness.prod_tsum_fubini g hg hgnn G.edgeFinset).1
  refine hprod.congr ?_
  intro m
  let base : ↥G.edgeFinset → ℝ :=
    fun e => ‖Sharpness.wEdge β J e.1 (m e)‖
  have hprod_eq_update :
      (∏ i : ↥G.edgeFinset, g i.1 (m i)) =
        ∏ i : ↥G.edgeFinset,
          Function.update base e0 (((m e0 + 1 : ℕ) : ℝ) * base e0) i := by
    refine Finset.prod_congr rfl ?_
    intro i _hi
    by_cases hi : i = e0
    · subst hi
      simp [g, base]
    · have hne : i.1 ≠ e0.1 := by
        intro h
        exact hi (Subtype.ext h)
      rw [Function.update_of_ne hi]
      simp [g, base, hne]
  have hupdate :
      (∏ i : ↥G.edgeFinset,
          Function.update base e0 (((m e0 + 1 : ℕ) : ℝ) * base e0) i) =
        (((m e0 + 1 : ℕ) : ℝ) * base e0) *
          ∏ i ∈ (Finset.univ : Finset ↥G.edgeFinset) \ {e0}, base i := by
    simpa using
      (Finset.prod_update_of_mem
        (s := (Finset.univ : Finset ↥G.edgeFinset))
        (i := e0) (f := base)
        (b := (((m e0 + 1 : ℕ) : ℝ) * base e0))
        (Finset.mem_univ e0))
  have herase :
      ∏ i ∈ (Finset.univ : Finset ↥G.edgeFinset) \ {e0}, base i =
        ∏ i ∈ (Finset.univ : Finset ↥G.edgeFinset).erase e0, base i := by
    rw [Finset.sdiff_singleton_eq_erase]
  calc
    (∏ i : ↥G.edgeFinset, g i.1 (m i))
        = (((m e0 + 1 : ℕ) : ℝ) * base e0) *
          ∏ i ∈ (Finset.univ : Finset ↥G.edgeFinset) \ {e0}, base i := by
          rw [hprod_eq_update, hupdate]
    _ = (((m e0 + 1 : ℕ) : ℝ) * base e0) *
          ∏ i ∈ (Finset.univ : Finset ↥G.edgeFinset).erase e0, base i := by
          rw [herase]
    _ = (((m e0 + 1 : ℕ) : ℝ) *
          (base e0 *
            ∏ i ∈ (Finset.univ : Finset ↥G.edgeFinset).erase e0, base i)) := by
          ring
    _ = (((m e0 + 1 : ℕ) : ℝ) * ∏ i : ↥G.edgeFinset, base i) := by
          rw [Finset.mul_prod_erase
            (s := (Finset.univ : Finset ↥G.edgeFinset))
            (f := base) (a := e0) (Finset.mem_univ e0)]
    _ = (((m e0 + 1 : ℕ) : ℝ) *
        ‖Sharpness.weight G β J (Sharpness.ofEdgeFun G m)‖) := by
          rw [Sharpness.weight_ofEdgeFun, norm_prod]
          rfl

set_option linter.style.longLine false in


theorem summable_edgeMultiplicitySucc_mul_currentSum_summand_norm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V)
    (e0 : ↥G.edgeFinset) :
    Summable (fun m : ↥G.edgeFinset → ℕ =>
      ‖(((m e0 + 1 : ℕ) : ℝ) *
        (if Sharpness.sources G (Sharpness.ofEdgeFun G m) = A then
          Sharpness.weight G β J (Sharpness.ofEdgeFun G m)
        else
          0))‖) := by
  have hdom : ∀ m : ↥G.edgeFinset → ℕ,
      ‖(((m e0 + 1 : ℕ) : ℝ) *
        (if Sharpness.sources G (Sharpness.ofEdgeFun G m) = A then
          Sharpness.weight G β J (Sharpness.ofEdgeFun G m)
        else
          0))‖ ≤
      (((m e0 + 1 : ℕ) : ℝ) *
        ‖Sharpness.weight G β J (Sharpness.ofEdgeFun G m)‖) := by
    intro m
    rw [norm_mul, Real.norm_eq_abs]
    rw [abs_of_nonneg (show 0 ≤ (((m e0 + 1 : ℕ) : ℝ) : ℝ) by positivity)]
    by_cases hsrc : Sharpness.sources G (Sharpness.ofEdgeFun G m) = A
    · rw [if_pos hsrc]
    · rw [if_neg hsrc, norm_zero, mul_zero]
      exact mul_nonneg (by positivity) (norm_nonneg _)
  have hnonneg : ∀ m : ↥G.edgeFinset → ℕ,
      0 ≤ ‖(((m e0 + 1 : ℕ) : ℝ) *
        (if Sharpness.sources G (Sharpness.ofEdgeFun G m) = A then
          Sharpness.weight G β J (Sharpness.ofEdgeFun G m)
        else
          0))‖ := by
    intro m
    exact norm_nonneg _
  exact Summable.of_nonneg_of_le hnonneg hdom
    (summable_edgeMultiplicitySucc_mul_norm_weight_ofEdgeFun G β J e0)

set_option linter.style.longLine false in


theorem summable_edgeMultiplicity_mul_currentSum_summand_norm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V)
    (e0 : ↥G.edgeFinset) :
    Summable (fun m : ↥G.edgeFinset → ℕ =>
      ‖(((m e0 : ℕ) : ℝ) *
        (if Sharpness.sources G (Sharpness.ofEdgeFun G m) = A then
          Sharpness.weight G β J (Sharpness.ofEdgeFun G m)
        else
          0))‖) := by
  have hdom : ∀ m : ↥G.edgeFinset → ℕ,
      ‖(((m e0 : ℕ) : ℝ) *
        (if Sharpness.sources G (Sharpness.ofEdgeFun G m) = A then
          Sharpness.weight G β J (Sharpness.ofEdgeFun G m)
        else
          0))‖ ≤
      ‖(((m e0 + 1 : ℕ) : ℝ) *
        (if Sharpness.sources G (Sharpness.ofEdgeFun G m) = A then
          Sharpness.weight G β J (Sharpness.ofEdgeFun G m)
        else
          0))‖ := by
    intro m
    rw [norm_mul, norm_mul, Real.norm_eq_abs]
    conv_rhs => rw [Real.norm_eq_abs]
    have hle :
        (((m e0 : ℕ) : ℝ) : ℝ) ≤ (((m e0 + 1 : ℕ) : ℝ) : ℝ) := by
      exact_mod_cast Nat.le_succ (m e0)
    have h0 : 0 ≤ (((m e0 : ℕ) : ℝ) : ℝ) := by positivity
    have h1 : 0 ≤ (((m e0 + 1 : ℕ) : ℝ) : ℝ) := by positivity
    rw [abs_of_nonneg h0, abs_of_nonneg h1]
    exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)
  have hnonneg : ∀ m : ↥G.edgeFinset → ℕ,
      0 ≤ ‖(((m e0 : ℕ) : ℝ) *
        (if Sharpness.sources G (Sharpness.ofEdgeFun G m) = A then
          Sharpness.weight G β J (Sharpness.ofEdgeFun G m)
        else
          0))‖ := by
    intro m
    exact norm_nonneg _
  exact Summable.of_nonneg_of_le hnonneg hdom
    (summable_edgeMultiplicitySucc_mul_currentSum_summand_norm G β J A e0)

theorem nat_add_add_one_le_succ_mul_succ (a b : ℕ) :
    a + b + 1 ≤ (a + 1) * (b + 1) := by
  calc
    a + b + 1 ≤ a * b + (a + b + 1) := Nat.le_add_left _ _
    _ = (a + 1) * (b + 1) := by ring

set_option linter.style.longLine false in


theorem summable_edgeMultiplicitySucc_mul_currentSum_pair_summand_norm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V)
    (e0 : ↥G.edgeFinset) :
    Summable (fun pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) =>
      ‖(((pq.1 e0 + pq.2 e0 + 1 : ℕ) : ℝ) *
        (currentSumProfileSummand G β J A pq.1 *
          currentSumProfileSummand G β J B pq.2))‖) := by
  classical
  set f : (↥G.edgeFinset → ℕ) → ℝ :=
    fun p => currentSumProfileSummand G β J A p with hf
  set g : (↥G.edgeFinset → ℕ) → ℝ :=
    fun q => currentSumProfileSummand G β J B q with hg
  have hfshift : Summable (fun p : ↥G.edgeFinset → ℕ =>
      ‖(((p e0 + 1 : ℕ) : ℝ) * f p)‖) := by
    simpa [hf, currentSumProfileSummand] using
      summable_edgeMultiplicitySucc_mul_currentSum_summand_norm G β J A e0
  have hgshift : Summable (fun q : ↥G.edgeFinset → ℕ =>
      ‖(((q e0 + 1 : ℕ) : ℝ) * g q)‖) := by
    simpa [hg, currentSumProfileSummand] using
      summable_edgeMultiplicitySucc_mul_currentSum_summand_norm G β J B e0
  have hprod : Summable
      (fun pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) =>
        ‖(((pq.1 e0 + 1 : ℕ) : ℝ) * f pq.1)‖ *
          ‖(((pq.2 e0 + 1 : ℕ) : ℝ) * g pq.2)‖) :=
    hfshift.mul_of_nonneg hgshift (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ hprod
  rintro ⟨p, q⟩
  change
    ‖(((p e0 + q e0 + 1 : ℕ) : ℝ) * (f p * g q))‖ ≤
      ‖(((p e0 + 1 : ℕ) : ℝ) * f p)‖ *
        ‖(((q e0 + 1 : ℕ) : ℝ) * g q)‖
  have hnat :
      p e0 + q e0 + 1 ≤ (p e0 + 1) * (q e0 + 1) :=
    nat_add_add_one_le_succ_mul_succ (p e0) (q e0)
  have hcast :
      (((p e0 + q e0 + 1 : ℕ) : ℝ) : ℝ) ≤
        (((p e0 + 1) * (q e0 + 1) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hfg_nonneg : 0 ≤ ‖f p‖ * ‖g q‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  calc
    ‖(((p e0 + q e0 + 1 : ℕ) : ℝ) * (f p * g q))‖
        = (((p e0 + q e0 + 1 : ℕ) : ℝ) : ℝ) * (‖f p‖ * ‖g q‖) := by
          rw [norm_mul, Real.norm_eq_abs,
            abs_of_nonneg
              (show 0 ≤ (((p e0 + q e0 + 1 : ℕ) : ℝ) : ℝ) by positivity),
            norm_mul]
    _ ≤ (((p e0 + 1) * (q e0 + 1) : ℕ) : ℝ) * (‖f p‖ * ‖g q‖) :=
      mul_le_mul_of_nonneg_right hcast hfg_nonneg
    _ = ‖(((p e0 + 1 : ℕ) : ℝ) * f p)‖ *
          ‖(((q e0 + 1 : ℕ) : ℝ) * g q)‖ := by
        rw [norm_mul, norm_mul]
        have hpnn :
            ‖(((p e0 + 1 : ℕ) : ℝ) : ℝ)‖ =
              (((p e0 + 1 : ℕ) : ℝ) : ℝ) := by
          rw [Real.norm_eq_abs]
          exact abs_of_nonneg (by positivity)
        have hqnn :
            ‖(((q e0 + 1 : ℕ) : ℝ) : ℝ)‖ =
              (((q e0 + 1 : ℕ) : ℝ) : ℝ) := by
          rw [Real.norm_eq_abs]
          exact abs_of_nonneg (by positivity)
        rw [hpnn, hqnn]
        norm_num
        ring

set_option linter.style.longLine false in


theorem summable_edgeMultiplicitySucc_mul_currentSum_split_sigma_norm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V)
    (e0 : ↥G.edgeFinset) :
    Summable (fun s : Sigma (fun m : ↥G.edgeFinset → ℕ =>
        {p : ↥G.edgeFinset → ℕ // p ≤ m}) =>
      ‖(((s.1 e0 + 1 : ℕ) : ℝ) *
        (currentSumProfileSummand G β J A s.2.1 *
          currentSumProfileSummand G β J B
            (fun e => s.1 e - s.2.1 e)))‖) := by
  classical
  rw [← (Sharpness.pairEquivSigma (E := ↥G.edgeFinset)).summable_iff]
  refine (summable_edgeMultiplicitySucc_mul_currentSum_pair_summand_norm
    G β J A B e0).congr ?_
  rintro ⟨p, q⟩
  simp only [Sharpness.pairEquivSigma, Equiv.coe_fn_mk]
  have hsub : (fun e => (p e + q e) - p e) = q := by
    ext e
    simp
  change
    ‖(((p e0 + q e0 + 1 : ℕ) : ℝ) *
      (currentSumProfileSummand G β J A p *
        currentSumProfileSummand G β J B q))‖ =
      ‖((((fun e => p e + q e) e0 + 1 : ℕ) : ℝ) *
        (currentSumProfileSummand G β J A p *
          currentSumProfileSummand G β J B
            (fun e => (p e + q e) - p e)))‖
  rw [hsub]

set_option linter.style.longLine false in

theorem summable_edgeMultiplicitySucc_mul_sourcePair_split_fiber_majorant
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V)
    (e0 : ↥G.edgeFinset) :
    Summable (fun m : ↥G.edgeFinset → ℕ =>
      ∑ K : {p : ↥G.edgeFinset → ℕ // p ≤ m},
        ‖(((m e0 + 1 : ℕ) : ℝ) *
          (currentSumProfileSummand G β J A K.1 *
            currentSumProfileSummand G β J B
              (fun e => m e - K.1 e)))‖) := by
  classical
  have hsig :=
    (summable_edgeMultiplicitySucc_mul_currentSum_split_sigma_norm
      G β J A B e0).sigma
  refine hsig.congr ?_
  intro m
  rw [tsum_fintype]

set_option linter.style.longLine false in


theorem summable_edgeMultiplicitySucc_mul_sourcePair_split_sum_norm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V)
    (e0 : ↥G.edgeFinset) :
    Summable (fun m : ↥G.edgeFinset → ℕ =>
      ‖(((m e0 + 1 : ℕ) : ℝ) *
        (∑ K : {p : ↥G.edgeFinset → ℕ // p ≤ m},
          currentSumProfileSummand G β J A K.1 *
            currentSumProfileSummand G β J B
              (fun e => m e - K.1 e)))‖) := by
  classical
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
    (summable_edgeMultiplicitySucc_mul_sourcePair_split_fiber_majorant
      G β J A B e0)
  intro m
  calc
    ‖(((m e0 + 1 : ℕ) : ℝ) *
        (∑ K : {p : ↥G.edgeFinset → ℕ // p ≤ m},
          currentSumProfileSummand G β J A K.1 *
            currentSumProfileSummand G β J B
              (fun e => m e - K.1 e)))‖
        = ‖∑ K : {p : ↥G.edgeFinset → ℕ // p ≤ m},
            (((m e0 + 1 : ℕ) : ℝ) *
              (currentSumProfileSummand G β J A K.1 *
                currentSumProfileSummand G β J B
                  (fun e => m e - K.1 e)))‖ := by
          rw [Finset.mul_sum]
    _ ≤ ∑ K : {p : ↥G.edgeFinset → ℕ // p ≤ m},
        ‖(((m e0 + 1 : ℕ) : ℝ) *
          (currentSumProfileSummand G β J A K.1 *
            currentSumProfileSummand G β J B
              (fun e => m e - K.1 e)))‖ := by
        simpa using
          norm_sum_le
            (s := (Finset.univ :
              Finset {p : ↥G.edgeFinset → ℕ // p ≤ m}))
            (f := fun K : {p : ↥G.edgeFinset → ℕ // p ≤ m} =>
              (((m e0 + 1 : ℕ) : ℝ) *
                (currentSumProfileSummand G β J A K.1 *
                  currentSumProfileSummand G β J B
                    (fun e => m e - K.1 e))))

set_option linter.style.longLine false in


theorem summable_edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_norm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V)
    (e0 : ↥G.edgeFinset) :
    Summable (fun m : ↥G.edgeFinset → ℕ =>
      ‖(((m e0 + 1 : ℕ) : ℝ) *
        edgeCopySourcePairSummand G β J A B m)‖) := by
  classical
  refine
    (summable_edgeMultiplicitySucc_mul_sourcePair_split_sum_norm
      G β J A B e0).congr ?_
  intro m
  have hbridge :=
    Sharpness.FluxEdgeCopy.sourcePair_superposition_bridge G β J A B m
  unfold edgeCopySourcePairSummand
  rw [← hbridge]
  simp [currentSumProfileSummand]

set_option linter.style.longLine false in


theorem summable_edgeMultiplicitySucc_mul_edgeCopySourcePairSummand
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V)
    (e0 : ↥G.edgeFinset) :
    Summable (fun m : ↥G.edgeFinset → ℕ =>
      (((m e0 + 1 : ℕ) : ℝ) *
        edgeCopySourcePairSummand G β J A B m)) := by
  exact Summable.of_norm
    (summable_edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_norm
      G β J A B e0)

set_option linter.style.longLine false in


theorem summable_edgeMultiplicity_mul_edgeCopySourcePairSummand_norm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V)
    (e0 : ↥G.edgeFinset) :
    Summable (fun m : ↥G.edgeFinset → ℕ =>
      ‖(((m e0 : ℕ) : ℝ) *
        edgeCopySourcePairSummand G β J A B m)‖) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
    (summable_edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_norm
      G β J A B e0)
  intro m
  rw [norm_mul, norm_mul, Real.norm_eq_abs]
  conv_rhs => rw [Real.norm_eq_abs]
  have hle :
      (((m e0 : ℕ) : ℝ) : ℝ) ≤ (((m e0 + 1 : ℕ) : ℝ) : ℝ) := by
    exact_mod_cast Nat.le_succ (m e0)
  have h0 : 0 ≤ (((m e0 : ℕ) : ℝ) : ℝ) := by positivity
  have h1 : 0 ≤ (((m e0 + 1 : ℕ) : ℝ) : ℝ) := by positivity
  rw [abs_of_nonneg h0, abs_of_nonneg h1]
  exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)

set_option linter.style.longLine false in


theorem summable_edgeMultiplicity_mul_edgeCopySourcePairSummand
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V)
    (e0 : ↥G.edgeFinset) :
    Summable (fun m : ↥G.edgeFinset → ℕ =>
      (((m e0 : ℕ) : ℝ) *
        edgeCopySourcePairSummand G β J A B m)) := by
  exact Summable.of_norm
    (summable_edgeMultiplicity_mul_edgeCopySourcePairSummand_norm
      G β J A B e0)

set_option linter.style.longLine false in


theorem edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_tsum_le_same_beta_forces_edgeMultiplicity_tsum_nonpos
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V)
    (e0 : ↥G.edgeFinset)
    (hle :
      (∑' m : ↥G.edgeFinset → ℕ,
        (((m e0 + 1 : ℕ) : ℝ) *
          edgeCopySourcePairSummand G β J A B m)) ≤
        edgeCopySourcePairSum G β J A B) :
    (∑' m : ↥G.edgeFinset → ℕ,
      (((m e0 : ℕ) : ℝ) *
        edgeCopySourcePairSummand G β J A B m)) ≤ 0 := by
  have hmoment :
      Summable (fun m : ↥G.edgeFinset → ℕ =>
        (((m e0 : ℕ) : ℝ) *
          edgeCopySourcePairSummand G β J A B m)) :=
    summable_edgeMultiplicity_mul_edgeCopySourcePairSummand G β J A B e0
  have hbase :
      Summable (fun m : ↥G.edgeFinset → ℕ =>
        edgeCopySourcePairSummand G β J A B m) :=
    edgeCopySourcePairSummand_summable G β J A B
  have hsplit :
      (∑' m : ↥G.edgeFinset → ℕ,
        (((m e0 + 1 : ℕ) : ℝ) *
          edgeCopySourcePairSummand G β J A B m)) =
        (∑' m : ↥G.edgeFinset → ℕ,
          (((m e0 : ℕ) : ℝ) *
            edgeCopySourcePairSummand G β J A B m)) +
          (∑' m : ↥G.edgeFinset → ℕ,
            edgeCopySourcePairSummand G β J A B m) := by
    calc
      (∑' m : ↥G.edgeFinset → ℕ,
        (((m e0 + 1 : ℕ) : ℝ) *
          edgeCopySourcePairSummand G β J A B m))
          =
        ∑' m : ↥G.edgeFinset → ℕ,
          ((((m e0 : ℕ) : ℝ) *
            edgeCopySourcePairSummand G β J A B m) +
            edgeCopySourcePairSummand G β J A B m) := by
          refine tsum_congr (fun m => ?_)
          rw [Nat.cast_add, Nat.cast_one]
          ring
      _ =
        (∑' m : ↥G.edgeFinset → ℕ,
          (((m e0 : ℕ) : ℝ) *
            edgeCopySourcePairSummand G β J A B m)) +
          (∑' m : ↥G.edgeFinset → ℕ,
            edgeCopySourcePairSummand G β J A B m) :=
        Summable.tsum_add hmoment hbase
  have hle' :
      (∑' m : ↥G.edgeFinset → ℕ,
        (((m e0 + 1 : ℕ) : ℝ) *
          edgeCopySourcePairSummand G β J A B m)) ≤
        (∑' m : ↥G.edgeFinset → ℕ,
          edgeCopySourcePairSummand G β J A B m) := by
    simpa [edgeCopySourcePairSum, edgeCopySourcePairSummand] using hle
  rw [hsplit] at hle'
  linarith

set_option linter.style.longLine false in


theorem edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_tsum_le_same_beta_forces_edgeMultiplicity_tsum_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβ : 0 ≤ β) (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (A B : Finset V) (e0 : ↥G.edgeFinset)
    (hle :
      (∑' m : ↥G.edgeFinset → ℕ,
        (((m e0 + 1 : ℕ) : ℝ) *
          edgeCopySourcePairSummand G β J A B m)) ≤
        edgeCopySourcePairSum G β J A B) :
    (∑' m : ↥G.edgeFinset → ℕ,
      (((m e0 : ℕ) : ℝ) *
        edgeCopySourcePairSummand G β J A B m)) = 0 := by
  have hle0 :=
    edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_tsum_le_same_beta_forces_edgeMultiplicity_tsum_nonpos
      G β J A B e0 hle
  have hnonneg :
      0 ≤
        (∑' m : ↥G.edgeFinset → ℕ,
          (((m e0 : ℕ) : ℝ) *
            edgeCopySourcePairSummand G β J A B m)) := by
    exact tsum_nonneg fun m =>
      mul_nonneg (by positivity)
        (edgeCopySourcePairSummand_nonneg G β J A B m hβ hJ)
  exact le_antisymm hle0 hnonneg

set_option linter.style.longLine false in


theorem summable_eq_zero_of_tsum_eq_zero_of_nonneg
    {α : Type*}
    {f : α → ℝ}
    (hsum : Summable f)
    (hnonneg : ∀ a, 0 ≤ f a)
    (htsum : (∑' a, f a) = 0)
    (a : α) :
    f a = 0 := by
  have hle :
      (∑ x ∈ ({a} : Finset α), f x) ≤ ∑' x, f x :=
    hsum.sum_le_tsum {a} (fun x _hx => hnonneg x)
  have hle0 : f a ≤ 0 := by
    simpa [htsum] using hle
  exact le_antisymm hle0 (hnonneg a)

set_option linter.style.longLine false in


theorem edgeMultiplicity_tsum_eq_zero_forces_edgeMultiplicity_summand_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβ : 0 ≤ β) (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (A B : Finset V) (e0 : ↥G.edgeFinset)
    (hzero :
      (∑' m : ↥G.edgeFinset → ℕ,
        (((m e0 : ℕ) : ℝ) *
          edgeCopySourcePairSummand G β J A B m)) = 0)
    (m : ↥G.edgeFinset → ℕ) :
    (((m e0 : ℕ) : ℝ) *
      edgeCopySourcePairSummand G β J A B m) = 0 := by
  exact
    summable_eq_zero_of_tsum_eq_zero_of_nonneg
      (summable_edgeMultiplicity_mul_edgeCopySourcePairSummand
        G β J A B e0)
      (fun m =>
        mul_nonneg (by positivity)
          (edgeCopySourcePairSummand_nonneg G β J A B m hβ hJ))
      hzero m

set_option linter.style.longLine false in


theorem edgeMultiplicity_tsum_eq_zero_forces_sourcePairSummand_eq_zero_of_pos
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβ : 0 ≤ β) (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (A B : Finset V) (e0 : ↥G.edgeFinset)
    (hzero :
      (∑' m : ↥G.edgeFinset → ℕ,
        (((m e0 : ℕ) : ℝ) *
          edgeCopySourcePairSummand G β J A B m)) = 0)
    (m : ↥G.edgeFinset → ℕ)
    (hmpos : 0 < m e0) :
    edgeCopySourcePairSummand G β J A B m = 0 := by
  have hpoint :=
    edgeMultiplicity_tsum_eq_zero_forces_edgeMultiplicity_summand_eq_zero
      G hβ J hJ A B e0 hzero m
  have hcoeff :
      (((m e0 : ℕ) : ℝ) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hmpos)
  exact (mul_eq_zero.mp hpoint).resolve_left hcoeff

set_option linter.style.longLine false in


theorem edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_tsum_le_same_beta_forces_sourcePairSummand_eq_zero_of_pos
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβ : 0 ≤ β) (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (A B : Finset V) (e0 : ↥G.edgeFinset)
    (hle :
      (∑' m : ↥G.edgeFinset → ℕ,
        (((m e0 + 1 : ℕ) : ℝ) *
          edgeCopySourcePairSummand G β J A B m)) ≤
        edgeCopySourcePairSum G β J A B)
    (m : ↥G.edgeFinset → ℕ)
    (hmpos : 0 < m e0) :
    edgeCopySourcePairSummand G β J A B m = 0 := by
  have hzero :=
    edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_tsum_le_same_beta_forces_edgeMultiplicity_tsum_eq_zero
      G hβ J hJ A B e0 hle
  exact
    edgeMultiplicity_tsum_eq_zero_forces_sourcePairSummand_eq_zero_of_pos
      G hβ J hJ A B e0 hzero m hmpos

set_option linter.style.longLine false in


theorem edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_tsum_le_same_beta_forces_edgeMultiplicity_eq_zero_of_summand_ne_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβ : 0 ≤ β) (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (A B : Finset V) (e0 : ↥G.edgeFinset)
    (hle :
      (∑' m : ↥G.edgeFinset → ℕ,
        (((m e0 + 1 : ℕ) : ℝ) *
          edgeCopySourcePairSummand G β J A B m)) ≤
        edgeCopySourcePairSum G β J A B)
    (m : ↥G.edgeFinset → ℕ)
    (hsummand_ne :
      edgeCopySourcePairSummand G β J A B m ≠ 0) :
    m e0 = 0 := by
  by_contra hmne
  have hmpos : 0 < m e0 := Nat.pos_of_ne_zero hmne
  have hzero :=
    edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_tsum_le_same_beta_forces_sourcePairSummand_eq_zero_of_pos
      G hβ J hJ A B e0 hle m hmpos
  exact hsummand_ne hzero

set_option linter.style.longLine false in


theorem edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_tsum_le_same_beta_not_of_pos_summand
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβ : 0 ≤ β) (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (A B : Finset V) (e0 : ↥G.edgeFinset)
    (m : ↥G.edgeFinset → ℕ)
    (hmpos : 0 < m e0)
    (hsummand_pos :
      0 < edgeCopySourcePairSummand G β J A B m) :
    ¬
      (∑' m : ↥G.edgeFinset → ℕ,
        (((m e0 + 1 : ℕ) : ℝ) *
          edgeCopySourcePairSummand G β J A B m)) ≤
        edgeCopySourcePairSum G β J A B := by
  intro hle
  have hzero :=
    edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_tsum_le_same_beta_forces_sourcePairSummand_eq_zero_of_pos
      G hβ J hJ A B e0 hle m hmpos
  exact (ne_of_gt hsummand_pos) hzero

set_option linter.style.longLine false in


theorem edgeCopySourcePairDataWeight_pos_of_pos_on_support
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβpos : 0 < β) (J : Sym2 V → ℝ)
    {A B : Finset V} (d : edgeCopySourcePairData G A B)
    (hJ : ∀ e : ↥G.edgeFinset, 0 < d.1 e → 0 < J e.1) :
    0 < edgeCopySourcePairDataWeight G β J d := by
  simpa [edgeCopySourcePairDataWeight] using
    weight_ofEdgeFun_pos_of_pos_on_support G β J hβpos d.1 hJ

set_option linter.style.longLine false in


theorem edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_tsum_le_same_beta_not_of_positive_dataWeight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβ : 0 ≤ β) (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (A B : Finset V) (e0 : ↥G.edgeFinset)
    (d : edgeCopySourcePairData G A B)
    (hmpos : 0 < d.1 e0)
    (hweight_pos : 0 < edgeCopySourcePairDataWeight G β J d) :
    ¬
      (∑' m : ↥G.edgeFinset → ℕ,
        (((m e0 + 1 : ℕ) : ℝ) *
          edgeCopySourcePairSummand G β J A B m)) ≤
        edgeCopySourcePairSum G β J A B := by
  have hsummand_pos :
      0 < edgeCopySourcePairSummand G β J A B d.1 :=
    lt_of_lt_of_le hweight_pos
      (edgeCopySourcePairDataWeight_le_summand G β J d
        (le_of_lt hweight_pos))
  exact
    edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_tsum_le_same_beta_not_of_pos_summand
      G hβ J hJ A B e0 d.1 hmpos hsummand_pos

set_option linter.style.longLine false in


theorem edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_tsum_le_same_beta_not_of_homogeneous_data
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβpos : 0 < β)
    (A B : Finset V) (e0 : ↥G.edgeFinset)
    (d : edgeCopySourcePairData G A B)
    (hmpos : 0 < d.1 e0) :
    ¬
      (∑' m : ↥G.edgeFinset → ℕ,
        (((m e0 + 1 : ℕ) : ℝ) *
          edgeCopySourcePairSummand G β (fun _ => 1) A B m)) ≤
        edgeCopySourcePairSum G β (fun _ => 1) A B := by
  have hweight_pos :
      0 < edgeCopySourcePairDataWeight G β (fun _ => 1) d :=
    edgeCopySourcePairDataWeight_pos_of_pos_on_support G hβpos
      (fun _ => 1) d (by intro e _he; norm_num)
  exact
    edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_tsum_le_same_beta_not_of_positive_dataWeight
      G (le_of_lt hβpos) (fun _ => 1) (by intro e; norm_num)
      A B e0 d hmpos hweight_pos

end Exact3D
end StatMech

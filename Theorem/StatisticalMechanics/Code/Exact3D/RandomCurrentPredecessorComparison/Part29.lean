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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part27
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

theorem edgeCopySourceSector_card_le_of_injection
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} {m m' : ↥G.edgeFinset → ℕ}
    (I : EdgeCopySourceSectorInjection G A B m m') :
    (edgeCopySourceSector G A m).card ≤
      (edgeCopySourceSector G B m').card := by
  let φ :
      Finset (Sharpness.FluxEdgeCopy.Copy G m) →
        Finset (Sharpness.FluxEdgeCopy.Copy G m') :=
    fun K =>
      if hK : K ∈ edgeCopySourceSector G A m then
        I.toFun K hK
      else
        ∅
  refine Finset.card_le_card_of_injOn φ ?_ ?_
  · intro K hK
    have hK' : K ∈ edgeCopySourceSector G A m := hK
    simpa [φ, hK'] using I.map_mem K hK'
  · intro K₁ hK₁ K₂ hK₂ hEq
    have hK₁' : K₁ ∈ edgeCopySourceSector G A m := hK₁
    have hK₂' : K₂ ∈ edgeCopySourceSector G A m := hK₂
    exact
      I.injective K₁ hK₁' K₂ hK₂'
        (by simpa [φ, hK₁', hK₂'] using hEq)


theorem edgeCopySourceSector_card_le_of_imageEmbedding
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} {m m' : ↥G.edgeFinset → ℕ}
    (I : EdgeCopySourceSectorImageEmbedding G A B m m') :
    (edgeCopySourceSector G A m).card ≤
      (edgeCopySourceSector G B m').card :=
  edgeCopySourceSector_card_le_of_injection G I.toSourceSectorInjection


theorem edgeCopySourceSector_card_le_of_insertEmbedding
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} {m m' : ↥G.edgeFinset → ℕ}
    (I : EdgeCopySourceSectorInsertEmbedding G A B m m') :
    (edgeCopySourceSector G A m).card ≤
      (edgeCopySourceSector G B m').card :=
  edgeCopySourceSector_card_le_of_injection G I.toSourceSectorInjection


theorem edgeCopySourcePairEmptyCollapsedMultiplicity_nonneg
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ↥G.edgeFinset → ℕ) :
    0 ≤ edgeCopySourcePairEmptyCollapsedMultiplicity G A m := by
  unfold edgeCopySourcePairEmptyCollapsedMultiplicity
  refine mul_nonneg ?_ (Nat.cast_nonneg _)
  by_cases hsrc :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM G m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) = A
  · rw [if_pos hsrc]
    norm_num
  · rw [if_neg hsrc]


theorem edgeCopySourcePairEmptyCollapsedMultiplicity_le_of_sourceSectorInjection
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} {m m' : ↥G.edgeFinset → ℕ}
    (I : EdgeCopySourceSectorInjection G A B m m') :
    edgeCopySourcePairEmptyCollapsedMultiplicity G A m ≤
      edgeCopySourcePairEmptyCollapsedMultiplicity G B m' := by
  by_cases hsrc :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM G m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) = A
  · have hsrc' := I.fullSource hsrc
    simpa [edgeCopySourcePairEmptyCollapsedMultiplicity, hsrc, hsrc'] using
      (show
        ((edgeCopySourceSector G A m).card : ℝ) ≤
          ((edgeCopySourceSector G B m').card : ℝ) from by
          exact_mod_cast edgeCopySourceSector_card_le_of_injection G I)
  · have hzero :
        edgeCopySourcePairEmptyCollapsedMultiplicity G A m = 0 := by
      simp [edgeCopySourcePairEmptyCollapsedMultiplicity, hsrc]
    rw [hzero]
    exact edgeCopySourcePairEmptyCollapsedMultiplicity_nonneg G B m'


theorem edgeCopySourcePairEmptyCollapsedMultiplicity_le_of_sourceSectorImageEmbedding
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} {m m' : ↥G.edgeFinset → ℕ}
    (I : EdgeCopySourceSectorImageEmbedding G A B m m') :
    edgeCopySourcePairEmptyCollapsedMultiplicity G A m ≤
      edgeCopySourcePairEmptyCollapsedMultiplicity G B m' :=
  edgeCopySourcePairEmptyCollapsedMultiplicity_le_of_sourceSectorInjection
    G I.toSourceSectorInjection


theorem edgeCopySourcePairEmptyCollapsedMultiplicity_le_of_sourceSectorInsertEmbedding
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} {m m' : ↥G.edgeFinset → ℕ}
    (I : EdgeCopySourceSectorInsertEmbedding G A B m m') :
    edgeCopySourcePairEmptyCollapsedMultiplicity G A m ≤
      edgeCopySourcePairEmptyCollapsedMultiplicity G B m' :=
  edgeCopySourcePairEmptyCollapsedMultiplicity_le_of_sourceSectorInjection
    G I.toSourceSectorInjection


theorem weight_ofEdgeFun_nonneg
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (m : ↥G.edgeFinset → ℕ) :
    0 ≤ Sharpness.weight G β J (Sharpness.ofEdgeFun G m) := by
  rw [Sharpness.weight_ofEdgeFun]
  exact Finset.prod_nonneg fun e _ =>
    div_nonneg (pow_nonneg (mul_nonneg hβ (hJ e.1)) _)
      (by positivity)


theorem weight_ofEdgeFun_increment
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ)
    (m : ↥G.edgeFinset → ℕ) (e : ↥G.edgeFinset) :
    (((m e + 1 : ℕ) : ℝ) *
        Sharpness.weight G β J
          (Sharpness.ofEdgeFun G (Function.update m e (m e + 1)))) =
      (β * J e.1) *
        Sharpness.weight G β J (Sharpness.ofEdgeFun G m) := by
  have hpos : 0 < (Function.update m e (m e + 1)) e := by
    rw [Function.update_self]
    omega
  have hdec :=
    weight_ofEdgeFun_decrement G β J
      (Function.update m e (m e + 1)) e hpos
  simpa [Function.update_self] using hdec


theorem weight_ofEdgeFun_singleEdge_homogeneous
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (e0 : ↥G.edgeFinset) :
    Sharpness.weight G β (fun _ => 1)
        (Sharpness.ofEdgeFun G (Function.update (fun _ : ↥G.edgeFinset => 0) e0 1)) =
      β := by
  rw [Sharpness.weight_ofEdgeFun]
  rw [Fintype.prod_eq_mul_prod_compl e0]
  simp only [Function.update_self, mul_one, pow_one,
    Nat.factorial_one, Nat.cast_one, div_one, Function.update_apply]
  have hprod :
      (∏ x ∈ ({e0}ᶜ : Finset ↥G.edgeFinset),
        β ^ (if x = e0 then 1 else 0) /
          (((if x = e0 then 1 else 0).factorial : ℕ) : ℝ)) = 1 := by
    refine Finset.prod_eq_one ?_
    intro x hx
    have hxnot : x ∉ ({e0} : Finset ↥G.edgeFinset) := by
      simpa [Finset.mem_compl] using hx
    have hxne : x ≠ e0 := by
      intro hxeq
      have hxmem : x ∈ ({e0} : Finset ↥G.edgeFinset) := by
        simp [hxeq]
      exact hxnot hxmem
    simp [hxne]
  rw [hprod]
  ring


theorem weight_ofEdgeFun_twoCopies_singleEdge_homogeneous
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (e0 : ↥G.edgeFinset) :
    Sharpness.weight G β (fun _ => 1)
        (Sharpness.ofEdgeFun G (Function.update (fun _ : ↥G.edgeFinset => 0) e0 2)) =
      β ^ 2 / 2 := by
  rw [Sharpness.weight_ofEdgeFun]
  rw [Fintype.prod_eq_mul_prod_compl e0]
  simp only [Function.update_self, mul_one, Function.update_apply]
  have hprod :
      (∏ x ∈ ({e0}ᶜ : Finset ↥G.edgeFinset),
        β ^ (if x = e0 then 2 else 0) /
          (((if x = e0 then 2 else 0).factorial : ℕ) : ℝ)) = 1 := by
    refine Finset.prod_eq_one ?_
    intro x hx
    have hxnot : x ∉ ({e0} : Finset ↥G.edgeFinset) := by
      simpa [Finset.mem_compl] using hx
    have hxne : x ≠ e0 := by
      intro hxeq
      have hxmem : x ∈ ({e0} : Finset ↥G.edgeFinset) := by
        simp [hxeq]
      exact hxnot hxmem
    simp [hxne]
  rw [hprod]
  norm_num

set_option linter.style.longLine false in


theorem weight_ofEdgeFun_singleEdgeCopies_homogeneous
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (e0 : ↥G.edgeFinset) (k : ℕ) :
    Sharpness.weight G β (fun _ => 1)
        (Sharpness.ofEdgeFun G (Function.update (fun _ : ↥G.edgeFinset => 0) e0 k)) =
      β ^ k / (Nat.factorial k : ℝ) := by
  rw [Sharpness.weight_ofEdgeFun]
  rw [Fintype.prod_eq_mul_prod_compl e0]
  simp only [Function.update_self, mul_one, Function.update_apply]
  have hprod :
      (∏ x ∈ ({e0}ᶜ : Finset ↥G.edgeFinset),
        β ^ (if x = e0 then k else 0) /
          (((if x = e0 then k else 0).factorial : ℕ) : ℝ)) = 1 := by
    refine Finset.prod_eq_one ?_
    intro x hx
    have hxnot : x ∉ ({e0} : Finset ↥G.edgeFinset) := by
      simpa [Finset.mem_compl] using hx
    have hxne : x ≠ e0 := by
      intro hxeq
      have hxmem : x ∈ ({e0} : Finset ↥G.edgeFinset) := by
        simp [hxeq]
      exact hxnot hxmem
    simp [hxne]
  rw [hprod]
  ring

theorem beta_pow_lt_factorial_succ_of_beta_lt_two
    {β : ℝ} (hβ : 0 ≤ β) (hβlt : β < 2) {k : ℕ} (hk : k ≠ 0) :
    β ^ k < (Nat.factorial (k + 1) : ℝ) := by
  have hpow_lt : β ^ k < (2 : ℝ) ^ k :=
    pow_lt_pow_left₀ hβlt hβ hk
  have hpow_le_nat : 2 ^ k ≤ Nat.factorial (k + 1) := by
    have h := Nat.factorial_mul_pow_le_factorial (m := 1) (n := k)
    simpa [Nat.factorial_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using h
  have hpow_le : (2 : ℝ) ^ k ≤ (Nat.factorial (k + 1) : ℝ) := by
    exact_mod_cast hpow_le_nat
  exact lt_of_lt_of_le hpow_lt hpow_le

theorem beta_pow_succ_div_factorial_succ_lt_beta_of_beta_lt_two
    {β : ℝ} (hβ : 0 < β) (hβlt : β < 2) {k : ℕ} (hk : k ≠ 0) :
    β ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) < β := by
  have hfac : 0 < (Nat.factorial (k + 1) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (k + 1)
  have hpow_lt :
      β ^ k < (Nat.factorial (k + 1) : ℝ) :=
    beta_pow_lt_factorial_succ_of_beta_lt_two hβ.le hβlt hk
  have hmul :
      β ^ (k + 1) < β * (Nat.factorial (k + 1) : ℝ) := by
    have hmul' :
        β ^ k * β < (Nat.factorial (k + 1) : ℝ) * β :=
      mul_lt_mul_of_pos_right hpow_lt hβ
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hmul'
  exact (div_lt_iff₀ hfac).2 hmul

set_option linter.style.longLine false in


theorem not_shiftedWeight_ge_beta_on_singleton_selectedEdgeOne_of_beta_lt_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβ : 0 < β) (hβlt : β < 2)
    (e0 : ↥G.edgeFinset) :
    ¬ (∀ m ∈ ({Function.update (fun _ : ↥G.edgeFinset => 0) e0 1} :
          Finset (↥G.edgeFinset → ℕ)),
        β ≤
          Sharpness.weight G β (fun _ => 1)
            (Sharpness.ofEdgeFun G (Function.update m e0 (m e0 + 1)))) := by
  intro hlower
  let m1 : ↥G.edgeFinset → ℕ :=
    Function.update (fun _ : ↥G.edgeFinset => 0) e0 1
  have hm1 :
      m1 ∈ ({Function.update (fun _ : ↥G.edgeFinset => 0) e0 1} :
        Finset (↥G.edgeFinset → ℕ)) := by
    simp [m1]
  have hle := hlower m1 hm1
  have hweight :
      Sharpness.weight G β (fun _ => 1)
          (Sharpness.ofEdgeFun G (Function.update m1 e0 (m1 e0 + 1))) =
        β ^ 2 / 2 := by
    simpa [m1, Function.update_self] using
      weight_ofEdgeFun_twoCopies_singleEdge_homogeneous G β e0
  have hle' : β ≤ β ^ 2 / 2 := by
    rw [hweight] at hle
    exact hle
  have hlt : β ^ 2 / 2 < β := by
    have hmul : β * β < 2 * β := mul_lt_mul_of_pos_right hβlt hβ
    nlinarith [hmul]
  exact (not_le_of_gt hlt) hle'

set_option linter.style.longLine false in


theorem not_shiftedWeight_ge_beta_on_singleton_selectedEdgeCopies_of_beta_lt_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβ : 0 < β) (hβlt : β < 2)
    (e0 : ↥G.edgeFinset) {k : ℕ} (hk : k ≠ 0) :
    ¬ (∀ m ∈ ({Function.update (fun _ : ↥G.edgeFinset => 0) e0 k} :
          Finset (↥G.edgeFinset → ℕ)),
        β ≤
          Sharpness.weight G β (fun _ => 1)
            (Sharpness.ofEdgeFun G (Function.update m e0 (m e0 + 1)))) := by
  intro hlower
  let mk : ↥G.edgeFinset → ℕ :=
    Function.update (fun _ : ↥G.edgeFinset => 0) e0 k
  have hmk :
      mk ∈ ({Function.update (fun _ : ↥G.edgeFinset => 0) e0 k} :
        Finset (↥G.edgeFinset → ℕ)) := by
    simp [mk]
  have hle := hlower mk hmk
  have hweight :
      Sharpness.weight G β (fun _ => 1)
          (Sharpness.ofEdgeFun G (Function.update mk e0 (mk e0 + 1))) =
        β ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) := by
    simpa [mk, Function.update_self] using
      weight_ofEdgeFun_singleEdgeCopies_homogeneous G β e0 (k + 1)
  have hle' : β ≤ β ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) := by
    rw [hweight] at hle
    exact hle
  have hlt :
      β ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) < β :=
    beta_pow_succ_div_factorial_succ_lt_beta_of_beta_lt_two hβ hβlt hk
  exact (not_le_of_gt hlt) hle'

set_option linter.style.longLine false in


theorem edgeMultiplicitySucc_mul_sum_edgeCopySourcePairSummand_increment_eq_betaJ_mul_sum_sourcePairWitnesses_card_mul_weight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V)
    (m : ↥G.edgeFinset → ℕ) (e : ↥G.edgeFinset) :
    (((m e + 1 : ℕ) : ℝ) *
        ∑ B : Finset V,
          edgeCopySourcePairSummand G β J A B
            (Function.update m e (m e + 1))) =
      (β * J e.1) *
        ∑ B : Finset V,
          (((edgeCopySourcePairWitnesses G A B
            (Function.update m e (m e + 1))).card : ℕ) : ℝ) *
            Sharpness.weight G β J (Sharpness.ofEdgeFun G m) := by
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro B _hB
  rw [edgeCopySourcePairSummand_eq_witness_card_mul_weight]
  have hinc := weight_ofEdgeFun_increment G β J m e
  calc
    (((m e + 1 : ℕ) : ℝ) *
      ((((edgeCopySourcePairWitnesses G A B
        (Function.update m e (m e + 1))).card : ℕ) : ℝ) *
        Sharpness.weight G β J
          (Sharpness.ofEdgeFun G (Function.update m e (m e + 1))))) =
        (((edgeCopySourcePairWitnesses G A B
          (Function.update m e (m e + 1))).card : ℕ) : ℝ) *
          ((((m e + 1 : ℕ) : ℝ) *
            Sharpness.weight G β J
              (Sharpness.ofEdgeFun G (Function.update m e (m e + 1))))) := by
      ring
    _ =
        (((edgeCopySourcePairWitnesses G A B
          (Function.update m e (m e + 1))).card : ℕ) : ℝ) *
          ((β * J e.1) *
            Sharpness.weight G β J (Sharpness.ofEdgeFun G m)) := by
      rw [hinc]
    _ =
        (β * J e.1) *
          ((((edgeCopySourcePairWitnesses G A B
            (Function.update m e (m e + 1))).card : ℕ) : ℝ) *
            Sharpness.weight G β J (Sharpness.ofEdgeFun G m)) := by
      ring

set_option linter.style.longLine false in


theorem summable_edgeMultiplicitySucc_mul_sum_edgeCopySourcePairSummand_increment
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V)
    (e0 : ↥G.edgeFinset) :
    Summable (fun m : ↥G.edgeFinset → ℕ =>
      (((m e0 + 1 : ℕ) : ℝ) *
        ∑ B : Finset V,
          edgeCopySourcePairSummand G β J A B
            (Function.update m e0 (m e0 + 1)))) := by
  classical
  have hsingle :
      ∀ B : Finset V,
        Summable (fun m : ↥G.edgeFinset → ℕ =>
          (((m e0 + 1 : ℕ) : ℝ) *
            edgeCopySourcePairSummand G β J A B
              (Function.update m e0 (m e0 + 1)))) := by
    intro B
    have hbase :
        Summable (fun M : ↥G.edgeFinset → ℕ =>
          (((M e0 : ℕ) : ℝ) *
            edgeCopySourcePairSummand G β J A B M)) :=
      summable_edgeMultiplicity_mul_edgeCopySourcePairSummand G β J A B e0
    simpa [Function.comp_def, Function.update_self] using
      (hbase.comp_injective
        (edgeMultiplicityIncrement_injective (ι := ↥G.edgeFinset) e0))
  have hsum :
      Summable (fun m : ↥G.edgeFinset → ℕ =>
        ∑ B ∈ (Finset.univ : Finset (Finset V)),
          (((m e0 + 1 : ℕ) : ℝ) *
            edgeCopySourcePairSummand G β J A B
              (Function.update m e0 (m e0 + 1)))) := by
    exact
      summable_sum
        (s := (Finset.univ : Finset (Finset V)))
        (f := fun B (m : ↥G.edgeFinset → ℕ) =>
          (((m e0 + 1 : ℕ) : ℝ) *
            edgeCopySourcePairSummand G β J A B
              (Function.update m e0 (m e0 + 1))))
        (fun B _hB => hsingle B)
  simpa [Finset.mul_sum] using hsum

set_option linter.style.longLine false in


theorem summable_edgeMultiplicity_mul_sum_edgeCopySourcePairSummand
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V)
    (e0 : ↥G.edgeFinset) :
    Summable (fun m : ↥G.edgeFinset → ℕ =>
      (((m e0 : ℕ) : ℝ) *
        ∑ B : Finset V,
          edgeCopySourcePairSummand G β J A B m)) := by
  classical
  have hsingle :
      ∀ B : Finset V,
        Summable (fun m : ↥G.edgeFinset → ℕ =>
          (((m e0 : ℕ) : ℝ) *
            edgeCopySourcePairSummand G β J A B m)) := by
    intro B
    exact summable_edgeMultiplicity_mul_edgeCopySourcePairSummand G β J A B e0
  have hsum :
      Summable (fun m : ↥G.edgeFinset → ℕ =>
        ∑ B ∈ (Finset.univ : Finset (Finset V)),
          (((m e0 : ℕ) : ℝ) *
            edgeCopySourcePairSummand G β J A B m)) := by
    exact
      summable_sum
        (s := (Finset.univ : Finset (Finset V)))
        (f := fun B (m : ↥G.edgeFinset → ℕ) =>
          (((m e0 : ℕ) : ℝ) *
            edgeCopySourcePairSummand G β J A B m))
        (fun B _hB => hsingle B)
  simpa [Finset.mul_sum] using hsum

set_option linter.style.longLine false in


theorem edgeMultiplicitySucc_mul_sum_edgeCopySourcePairSummand_increment_tsum_le_sum_sourcePairSum_two_beta
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβ : 0 ≤ β) (A : Finset V)
    (e0 : ↥G.edgeFinset) :
    (∑' m : ↥G.edgeFinset → ℕ,
      (((m e0 + 1 : ℕ) : ℝ) *
        ∑ B : Finset V,
          edgeCopySourcePairSummand G β (fun _ => 1) A B
            (Function.update m e0 (m e0 + 1)))) ≤
      ∑ B : Finset V,
        edgeCopySourcePairSum G (2 * β) (fun _ => 1) A B := by
  classical
  have hupdate :
      Summable (fun m : ↥G.edgeFinset → ℕ =>
        (((m e0 + 1 : ℕ) : ℝ) *
          ∑ B : Finset V,
            edgeCopySourcePairSummand G β (fun _ => 1) A B
              (Function.update m e0 (m e0 + 1)))) :=
    summable_edgeMultiplicitySucc_mul_sum_edgeCopySourcePairSummand_increment
      G β (fun _ => 1) A e0
  have hcoord :
      Summable (fun m : ↥G.edgeFinset → ℕ =>
        (((m e0 : ℕ) : ℝ) *
          ∑ B : Finset V,
            edgeCopySourcePairSummand G β (fun _ => 1) A B m)) :=
    summable_edgeMultiplicity_mul_sum_edgeCopySourcePairSummand
      G β (fun _ => 1) A e0
  have himage :
      (∑' m : ↥G.edgeFinset → ℕ,
        (((m e0 + 1 : ℕ) : ℝ) *
          ∑ B : Finset V,
            edgeCopySourcePairSummand G β (fun _ => 1) A B
              (Function.update m e0 (m e0 + 1)))) ≤
        ∑' M : ↥G.edgeFinset → ℕ,
          (((M e0 : ℕ) : ℝ) *
            ∑ B : Finset V,
              edgeCopySourcePairSummand G β (fun _ => 1) A B M) := by
    refine
      Summable.tsum_le_tsum_of_inj
        (fun m : ↥G.edgeFinset → ℕ => Function.update m e0 (m e0 + 1))
        (edgeMultiplicityIncrement_injective (ι := ↥G.edgeFinset) e0)
        ?_ ?_ hupdate hcoord
    · intro M _hM
      exact
        mul_nonneg (by positivity)
          (Finset.sum_nonneg fun B _hB =>
            edgeCopySourcePairSummand_nonneg G β (fun _ => 1) A B M hβ
              (by intro e; norm_num))
    · intro m
      simp [Function.update_self]
  have htwo_summable :
      Summable (fun m : ↥G.edgeFinset → ℕ =>
        ∑ B : Finset V,
          edgeCopySourcePairSummand G (2 * β) (fun _ => 1) A B m) := by
    have hsum :
        Summable (fun m : ↥G.edgeFinset → ℕ =>
          ∑ B ∈ (Finset.univ : Finset (Finset V)),
            edgeCopySourcePairSummand G (2 * β) (fun _ => 1) A B m) := by
      exact
        summable_sum
          (s := (Finset.univ : Finset (Finset V)))
          (f := fun B (m : ↥G.edgeFinset → ℕ) =>
            edgeCopySourcePairSummand G (2 * β) (fun _ => 1) A B m)
          (fun B _hB =>
            edgeCopySourcePairSummand_summable G (2 * β) (fun _ => 1) A B)
    simpa using hsum
  have hcoord_le_two :
      (∑' M : ↥G.edgeFinset → ℕ,
        (((M e0 : ℕ) : ℝ) *
          ∑ B : Finset V,
            edgeCopySourcePairSummand G β (fun _ => 1) A B M)) ≤
        ∑' M : ↥G.edgeFinset → ℕ,
          ∑ B : Finset V,
            edgeCopySourcePairSummand G (2 * β) (fun _ => 1) A B M := by
    refine hcoord.tsum_le_tsum ?_ htwo_summable
    intro M
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro B _hB
    exact edgeMultiplicity_mul_edgeCopySourcePairSummand_le_two_beta
      G hβ A B M e0
  have htwo_tsum :
      (∑' M : ↥G.edgeFinset → ℕ,
        ∑ B : Finset V,
          edgeCopySourcePairSummand G (2 * β) (fun _ => 1) A B M) =
        ∑ B : Finset V,
          edgeCopySourcePairSum G (2 * β) (fun _ => 1) A B := by
    have hhas :
        HasSum
          (fun M : ↥G.edgeFinset → ℕ =>
            ∑ B ∈ (Finset.univ : Finset (Finset V)),
              edgeCopySourcePairSummand G (2 * β) (fun _ => 1) A B M)
          (∑ B ∈ (Finset.univ : Finset (Finset V)),
            edgeCopySourcePairSum G (2 * β) (fun _ => 1) A B) := by
      refine hasSum_sum ?_
      intro B _hB
      rw [edgeCopySourcePairSum]
      exact
        (edgeCopySourcePairSummand_summable G (2 * β) (fun _ => 1) A B).hasSum
    simpa using hhas.tsum_eq
  exact himage.trans (hcoord_le_two.trans (le_of_eq htwo_tsum))

set_option linter.style.longLine false in


theorem edgeMultiplicitySucc_mul_sum_edgeCopySourcePairSummand_increment_finset_sum_le_sum_sourcePairSum_two_beta
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβ : 0 ≤ β) (A : Finset V)
    (e0 : ↥G.edgeFinset)
    (Ω : Finset (↥G.edgeFinset → ℕ)) :
    (∑ m ∈ Ω,
      (((m e0 + 1 : ℕ) : ℝ) *
        ∑ B : Finset V,
          edgeCopySourcePairSummand G β (fun _ => 1) A B
            (Function.update m e0 (m e0 + 1)))) ≤
      ∑ B : Finset V,
        edgeCopySourcePairSum G (2 * β) (fun _ => 1) A B := by
  have hsum :
      Summable (fun m : ↥G.edgeFinset → ℕ =>
        (((m e0 + 1 : ℕ) : ℝ) *
          ∑ B : Finset V,
            edgeCopySourcePairSummand G β (fun _ => 1) A B
              (Function.update m e0 (m e0 + 1)))) :=
    summable_edgeMultiplicitySucc_mul_sum_edgeCopySourcePairSummand_increment
      G β (fun _ => 1) A e0
  calc
    (∑ m ∈ Ω,
      (((m e0 + 1 : ℕ) : ℝ) *
        ∑ B : Finset V,
          edgeCopySourcePairSummand G β (fun _ => 1) A B
            (Function.update m e0 (m e0 + 1)))) ≤
        ∑' m : ↥G.edgeFinset → ℕ,
          (((m e0 + 1 : ℕ) : ℝ) *
            ∑ B : Finset V,
              edgeCopySourcePairSummand G β (fun _ => 1) A B
                (Function.update m e0 (m e0 + 1))) :=
      hsum.sum_le_tsum Ω
        (fun m _hm =>
          mul_nonneg (by positivity)
            (Finset.sum_nonneg fun B _hB =>
              edgeCopySourcePairSummand_nonneg G β (fun _ => 1) A B
                (Function.update m e0 (m e0 + 1)) hβ
                (by intro e; norm_num)))
    _ ≤
        ∑ B : Finset V,
          edgeCopySourcePairSum G (2 * β) (fun _ => 1) A B :=
      edgeMultiplicitySucc_mul_sum_edgeCopySourcePairSummand_increment_tsum_le_sum_sourcePairSum_two_beta
        G hβ A e0


theorem weight_ofEdgeFun_le_of_edge_increment_of_betaJ_le_count
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (m : ↥G.edgeFinset → ℕ) (e : ↥G.edgeFinset)
    (hβJ_le : β * J e.1 ≤ (((m e + 1 : ℕ) : ℝ))) :
    Sharpness.weight G β J
        (Sharpness.ofEdgeFun G (Function.update m e (m e + 1))) ≤
      Sharpness.weight G β J (Sharpness.ofEdgeFun G m) := by
  let c : ℝ := ((m e + 1 : ℕ) : ℝ)
  have hcpos : 0 < c := by
    dsimp [c]
    positivity
  have hsrc_nonneg :
      0 ≤ Sharpness.weight G β J (Sharpness.ofEdgeFun G m) :=
    weight_ofEdgeFun_nonneg G β J hβ hJ m
  have hmul :
      c * Sharpness.weight G β J
          (Sharpness.ofEdgeFun G (Function.update m e (m e + 1))) ≤
        c * Sharpness.weight G β J (Sharpness.ofEdgeFun G m) := by
    calc
      c * Sharpness.weight G β J
          (Sharpness.ofEdgeFun G (Function.update m e (m e + 1))) =
        (β * J e.1) *
          Sharpness.weight G β J (Sharpness.ofEdgeFun G m) := by
          simpa [c] using weight_ofEdgeFun_increment G β J m e
      _ ≤ c * Sharpness.weight G β J (Sharpness.ofEdgeFun G m) :=
          mul_le_mul_of_nonneg_right hβJ_le hsrc_nonneg
  exact le_of_mul_le_mul_left hmul hcpos


theorem weight_ofEdgeFun_eq_of_ofEdgeFun_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ)
    {m m' : ↥G.edgeFinset → ℕ}
    (h :
      Sharpness.ofEdgeFun G m = Sharpness.ofEdgeFun G m') :
    Sharpness.weight G β J (Sharpness.ofEdgeFun G m) =
      Sharpness.weight G β J (Sharpness.ofEdgeFun G m') := by
  rw [h]


theorem weight_ofEdgeFun_le_of_ofEdgeFun_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ)
    {m m' : ↥G.edgeFinset → ℕ}
    (h :
      Sharpness.ofEdgeFun G m = Sharpness.ofEdgeFun G m') :
    Sharpness.weight G β J (Sharpness.ofEdgeFun G m) ≤
      Sharpness.weight G β J (Sharpness.ofEdgeFun G m') :=
  le_of_eq (weight_ofEdgeFun_eq_of_ofEdgeFun_eq G β J h)


theorem ofEdgeFun_eq_of_edge_multiplicity_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {m m' : ↥G.edgeFinset → ℕ}
    (h : ∀ e, m e = m' e) :
    Sharpness.ofEdgeFun G m = Sharpness.ofEdgeFun G m' := by
  have hm : m = m' := funext h
  subst m'
  rfl


theorem weight_ofEdgeFun_eq_of_edge_multiplicity_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ)
    {m m' : ↥G.edgeFinset → ℕ}
    (h : ∀ e, m e = m' e) :
    Sharpness.weight G β J (Sharpness.ofEdgeFun G m) =
      Sharpness.weight G β J (Sharpness.ofEdgeFun G m') :=
  weight_ofEdgeFun_eq_of_ofEdgeFun_eq G β J
    (ofEdgeFun_eq_of_edge_multiplicity_eq G h)


theorem weight_ofEdgeFun_le_of_edge_multiplicity_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ)
    {m m' : ↥G.edgeFinset → ℕ}
    (h : ∀ e, m e = m' e) :
    Sharpness.weight G β J (Sharpness.ofEdgeFun G m) ≤
      Sharpness.weight G β J (Sharpness.ofEdgeFun G m') :=
  le_of_eq (weight_ofEdgeFun_eq_of_edge_multiplicity_eq G β J h)


theorem weight_ofEdgeFun_eq_of_edge_equiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ)
    {m m' : ↥G.edgeFinset → ℕ}
    (σ : ↥G.edgeFinset ≃ ↥G.edgeFinset)
    (hJ : ∀ e, J (σ e).1 = J e.1)
    (hm : ∀ e, m' (σ e) = m e) :
    Sharpness.weight G β J (Sharpness.ofEdgeFun G m) =
      Sharpness.weight G β J (Sharpness.ofEdgeFun G m') := by
  rw [Sharpness.weight_ofEdgeFun, Sharpness.weight_ofEdgeFun]
  let term : ↥G.edgeFinset → ℝ :=
    fun e => (β * J e.1) ^ (m' e) / Nat.factorial (m' e)
  calc
    (∏ e : ↥G.edgeFinset, (β * J e.1) ^ (m e) / Nat.factorial (m e))
        =
      ∏ e : ↥G.edgeFinset,
        (β * J (σ e).1) ^ (m' (σ e)) / Nat.factorial (m' (σ e)) := by
        refine Finset.prod_congr rfl ?_
        intro e _
        rw [hJ e, hm e]
    _ = ∏ e : ↥G.edgeFinset, term e := by
        simpa [term] using
          (Equiv.prod_comp σ term)
    _ =
      ∏ e : ↥G.edgeFinset,
        (β * J e.1) ^ (m' e) / Nat.factorial (m' e) := rfl


theorem weight_ofEdgeFun_le_of_edge_equiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ)
    {m m' : ↥G.edgeFinset → ℕ}
    (σ : ↥G.edgeFinset ≃ ↥G.edgeFinset)
    (hJ : ∀ e, J (σ e).1 = J e.1)
    (hm : ∀ e, m' (σ e) = m e) :
    Sharpness.weight G β J (Sharpness.ofEdgeFun G m) ≤
      Sharpness.weight G β J (Sharpness.ofEdgeFun G m') :=
  le_of_eq (weight_ofEdgeFun_eq_of_edge_equiv G β J σ hJ hm)


theorem weight_ofEdgeFun_eq_of_edge_equiv_homogeneous
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) {m m' : ↥G.edgeFinset → ℕ}
    (σ : ↥G.edgeFinset ≃ ↥G.edgeFinset)
    (hm : ∀ e, m' (σ e) = m e) :
    Sharpness.weight G β (fun _ => 1) (Sharpness.ofEdgeFun G m) =
      Sharpness.weight G β (fun _ => 1) (Sharpness.ofEdgeFun G m') :=
  weight_ofEdgeFun_eq_of_edge_equiv G β (fun _ => 1) σ (by intro e; rfl) hm


theorem weight_ofEdgeFun_le_of_edge_equiv_homogeneous
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) {m m' : ↥G.edgeFinset → ℕ}
    (σ : ↥G.edgeFinset ≃ ↥G.edgeFinset)
    (hm : ∀ e, m' (σ e) = m e) :
    Sharpness.weight G β (fun _ => 1) (Sharpness.ofEdgeFun G m) ≤
      Sharpness.weight G β (fun _ => 1) (Sharpness.ofEdgeFun G m') :=
  le_of_eq (weight_ofEdgeFun_eq_of_edge_equiv_homogeneous G β σ hm)


theorem edgeCopyFullSources_eq_of_edge_multiplicity_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {m m' : ↥G.edgeFinset → ℕ}
    (h : ∀ e, m e = m' e) :
    Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM G m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) =
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM G m')
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m')) := by
  rw [Sharpness.FluxEdgeCopy.sources_eq,
    Sharpness.FluxEdgeCopy.sources_eq,
    Sharpness.FluxEdgeCopy.profileFlux_univ,
    Sharpness.FluxEdgeCopy.profileFlux_univ]
  exact congrArg (fun n => Sharpness.sources G n)
    (ofEdgeFun_eq_of_edge_multiplicity_eq G h)


theorem EdgeCopySourceSectorImageEmbedding.source_eq_of_edge_multiplicity_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A B : Finset V} {m m' : ↥G.edgeFinset → ℕ}
    (I : EdgeCopySourceSectorImageEmbedding G A B m m')
    (hm : ∀ e, m e = m' e)
    (hsrc :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM G m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) = A) :
    A = B := by
  calc
    A =
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G m)
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) := hsrc.symm
    _ =
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G m')
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m')) :=
        edgeCopyFullSources_eq_of_edge_multiplicity_eq G hm
    _ = B := I.fullSource hsrc


theorem EdgeCopySourceSectorImageEmbedding.not_fullSource_of_source_ne_of_edge_multiplicity_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A B : Finset V} {m m' : ↥G.edgeFinset → ℕ}
    (I : EdgeCopySourceSectorImageEmbedding G A B m m')
    (hm : ∀ e, m e = m' e)
    (hAB : A ≠ B) :
    ¬ Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM G m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) = A := by
  intro hsrc
  exact hAB (I.source_eq_of_edge_multiplicity_eq hm hsrc)

set_option linter.style.longLine false in


theorem edgeCopyFullSources_eq_of_edge_equiv_endpoint_preserving
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {m m' : ↥G.edgeFinset → ℕ}
    (σ : ↥G.edgeFinset ≃ ↥G.edgeFinset)
    (hm : ∀ e, m' (σ e) = m e)
    (hends : ∀ e, (σ e).1 = e.1) :
    Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM G m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) =
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM G m')
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m')) := by
  let copyEquiv := edgeCopyEquivOfEdgeEquiv G σ hm
  have hcopy :
      Function.Injective copyEquiv :=
    copyEquiv.injective
  have hends_copy :
      ∀ i,
        Sharpness.FluxEdgeCopy.endsM G m' (copyEquiv i) =
          Sym2.map (Equiv.refl V)
            (Sharpness.FluxEdgeCopy.endsM G m i) := by
    intro i
    simpa [copyEquiv, Sym2.map] using
      edgeCopyEquivOfEdgeEquiv_ends
        (Equiv.refl V) σ hm (by intro e; simpa using hends e) i
  have hmap :=
    randomCurrent_sources_image_of_vertexEquiv
      (Sharpness.FluxEdgeCopy.endsM G m)
      (Sharpness.FluxEdgeCopy.endsM G m')
      (Equiv.refl V) copyEquiv hcopy hends_copy
      (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m))
  have huniv :
      (Finset.univ :
          Finset (Sharpness.FluxEdgeCopy.Copy G m)).image copyEquiv =
        (Finset.univ :
          Finset (Sharpness.FluxEdgeCopy.Copy G m')) := by
    ext i
    simp
  rw [huniv] at hmap
  simpa [Sym2.map] using hmap.symm

set_option linter.style.longLine false in


theorem EdgeCopySourceSectorImageEmbedding.source_eq_of_edge_equiv_endpoint_preserving
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A B : Finset V} {m m' : ↥G.edgeFinset → ℕ}
    (I : EdgeCopySourceSectorImageEmbedding G A B m m')
    (σ : ↥G.edgeFinset ≃ ↥G.edgeFinset)
    (hm : ∀ e, m' (σ e) = m e)
    (hends : ∀ e, (σ e).1 = e.1)
    (hsrc :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM G m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) = A) :
    A = B := by
  calc
    A =
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G m)
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) := hsrc.symm
    _ =
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G m')
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m')) :=
        edgeCopyFullSources_eq_of_edge_equiv_endpoint_preserving G σ hm hends
    _ = B := I.fullSource hsrc

set_option linter.style.longLine false in


theorem EdgeCopySourceSectorImageEmbedding.not_fullSource_of_source_ne_of_edge_equiv_endpoint_preserving
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A B : Finset V} {m m' : ↥G.edgeFinset → ℕ}
    (I : EdgeCopySourceSectorImageEmbedding G A B m m')
    (σ : ↥G.edgeFinset ≃ ↥G.edgeFinset)
    (hm : ∀ e, m' (σ e) = m e)
    (hends : ∀ e, (σ e).1 = e.1)
    (hAB : A ≠ B) :
    ¬ Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM G m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) = A := by
  intro hsrc
  exact hAB
    (I.source_eq_of_edge_equiv_endpoint_preserving σ hm hends hsrc)


theorem edgeCopySourcePairEmptyCollapsedTerm_nonneg
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (m : ↥G.edgeFinset → ℕ) :
    0 ≤ edgeCopySourcePairEmptyCollapsedTerm G β J A m := by
  rw [edgeCopySourcePairEmptyCollapsedTerm_eq_multiplicity_mul_weight]
  exact
    mul_nonneg
      (edgeCopySourcePairEmptyCollapsedMultiplicity_nonneg G A m)
      (weight_ofEdgeFun_nonneg G β J hβ hJ m)


theorem edgeCopySourcePairEmptyCollapsedTerm_le_of_multiplicity_le_of_weight_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) {A B : Finset V}
    (m m' : ↥G.edgeFinset → ℕ)
    (hweight_nonneg :
      0 ≤ Sharpness.weight G β J (Sharpness.ofEdgeFun G m))
    (hmult :
      edgeCopySourcePairEmptyCollapsedMultiplicity G A m ≤
        edgeCopySourcePairEmptyCollapsedMultiplicity G B m')
    (hweight :
      Sharpness.weight G β J (Sharpness.ofEdgeFun G m) ≤
        Sharpness.weight G β J (Sharpness.ofEdgeFun G m')) :
    edgeCopySourcePairEmptyCollapsedTerm G β J A m ≤
      edgeCopySourcePairEmptyCollapsedTerm G β J B m' := by
  rw [edgeCopySourcePairEmptyCollapsedTerm_eq_multiplicity_mul_weight]
  rw [edgeCopySourcePairEmptyCollapsedTerm_eq_multiplicity_mul_weight]
  calc
    edgeCopySourcePairEmptyCollapsedMultiplicity G A m *
        Sharpness.weight G β J (Sharpness.ofEdgeFun G m)
        ≤
      edgeCopySourcePairEmptyCollapsedMultiplicity G B m' *
        Sharpness.weight G β J (Sharpness.ofEdgeFun G m) :=
      mul_le_mul_of_nonneg_right hmult hweight_nonneg
    _ ≤
      edgeCopySourcePairEmptyCollapsedMultiplicity G B m' *
        Sharpness.weight G β J (Sharpness.ofEdgeFun G m') :=
      mul_le_mul_of_nonneg_left hweight
        (edgeCopySourcePairEmptyCollapsedMultiplicity_nonneg G B m')


theorem edgeCopySourcePairEmptyCollapsedTerm_le_of_sourceSectorInjection_of_weight_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) {A B : Finset V}
    (m m' : ↥G.edgeFinset → ℕ)
    (hweight_nonneg :
      0 ≤ Sharpness.weight G β J (Sharpness.ofEdgeFun G m))
    (I : EdgeCopySourceSectorInjection G A B m m')
    (hweight :
      Sharpness.weight G β J (Sharpness.ofEdgeFun G m) ≤
        Sharpness.weight G β J (Sharpness.ofEdgeFun G m')) :
    edgeCopySourcePairEmptyCollapsedTerm G β J A m ≤
      edgeCopySourcePairEmptyCollapsedTerm G β J B m' :=
  edgeCopySourcePairEmptyCollapsedTerm_le_of_multiplicity_le_of_weight_le
    G β J m m' hweight_nonneg
    (edgeCopySourcePairEmptyCollapsedMultiplicity_le_of_sourceSectorInjection G I)
    hweight


theorem edgeCopySourcePairEmptyCollapsedTerm_le_of_sourceSectorImageEmbedding_of_weight_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) {A B : Finset V}
    (m m' : ↥G.edgeFinset → ℕ)
    (hweight_nonneg :
      0 ≤ Sharpness.weight G β J (Sharpness.ofEdgeFun G m))
    (I : EdgeCopySourceSectorImageEmbedding G A B m m')
    (hweight :
      Sharpness.weight G β J (Sharpness.ofEdgeFun G m) ≤
        Sharpness.weight G β J (Sharpness.ofEdgeFun G m')) :
    edgeCopySourcePairEmptyCollapsedTerm G β J A m ≤
      edgeCopySourcePairEmptyCollapsedTerm G β J B m' :=
  edgeCopySourcePairEmptyCollapsedTerm_le_of_sourceSectorInjection_of_weight_le
    G β J m m' hweight_nonneg I.toSourceSectorInjection hweight


theorem edgeCopySourcePairEmptyCollapsedTerm_le_of_sourceSectorInsertEmbedding_of_weight_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) {A B : Finset V}
    (m m' : ↥G.edgeFinset → ℕ)
    (hweight_nonneg :
      0 ≤ Sharpness.weight G β J (Sharpness.ofEdgeFun G m))
    (I : EdgeCopySourceSectorInsertEmbedding G A B m m')
    (hweight :
      Sharpness.weight G β J (Sharpness.ofEdgeFun G m) ≤
        Sharpness.weight G β J (Sharpness.ofEdgeFun G m')) :
    edgeCopySourcePairEmptyCollapsedTerm G β J A m ≤
      edgeCopySourcePairEmptyCollapsedTerm G β J B m' :=
  edgeCopySourcePairEmptyCollapsedTerm_le_of_sourceSectorInjection_of_weight_le
    G β J m m' hweight_nonneg I.toSourceSectorInjection hweight


theorem edgeCopySourcePairEmptyCollapsedTerm_le_of_sourceSectorInjection_of_ofEdgeFun_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) {A B : Finset V}
    (m m' : ↥G.edgeFinset → ℕ)
    (hweight_nonneg :
      0 ≤ Sharpness.weight G β J (Sharpness.ofEdgeFun G m))
    (I : EdgeCopySourceSectorInjection G A B m m')
    (h :
      Sharpness.ofEdgeFun G m = Sharpness.ofEdgeFun G m') :
    edgeCopySourcePairEmptyCollapsedTerm G β J A m ≤
      edgeCopySourcePairEmptyCollapsedTerm G β J B m' :=
  edgeCopySourcePairEmptyCollapsedTerm_le_of_sourceSectorInjection_of_weight_le
    G β J m m' hweight_nonneg I
    (weight_ofEdgeFun_le_of_ofEdgeFun_eq G β J h)


theorem edgeCopySourcePairEmptyCollapsedTerm_le_of_sourceSectorImageEmbedding_of_ofEdgeFun_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) {A B : Finset V}
    (m m' : ↥G.edgeFinset → ℕ)
    (hweight_nonneg :
      0 ≤ Sharpness.weight G β J (Sharpness.ofEdgeFun G m))
    (I : EdgeCopySourceSectorImageEmbedding G A B m m')
    (h :
      Sharpness.ofEdgeFun G m = Sharpness.ofEdgeFun G m') :
    edgeCopySourcePairEmptyCollapsedTerm G β J A m ≤
      edgeCopySourcePairEmptyCollapsedTerm G β J B m' :=
  edgeCopySourcePairEmptyCollapsedTerm_le_of_sourceSectorImageEmbedding_of_weight_le
    G β J m m' hweight_nonneg I
    (weight_ofEdgeFun_le_of_ofEdgeFun_eq G β J h)


theorem edgeCopySourcePairEmptyCollapsedTerm_le_of_sourceSectorInsertEmbedding_of_ofEdgeFun_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) {A B : Finset V}
    (m m' : ↥G.edgeFinset → ℕ)
    (hweight_nonneg :
      0 ≤ Sharpness.weight G β J (Sharpness.ofEdgeFun G m))
    (I : EdgeCopySourceSectorInsertEmbedding G A B m m')
    (h :
      Sharpness.ofEdgeFun G m = Sharpness.ofEdgeFun G m') :
    edgeCopySourcePairEmptyCollapsedTerm G β J A m ≤
      edgeCopySourcePairEmptyCollapsedTerm G β J B m' :=
  edgeCopySourcePairEmptyCollapsedTerm_le_of_sourceSectorInsertEmbedding_of_weight_le
    G β J m m' hweight_nonneg I
    (weight_ofEdgeFun_le_of_ofEdgeFun_eq G β J h)


theorem edgeCopySourcePairEmptyCollapsedTerm_le_of_sourceSectorInjection_of_edge_multiplicity_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) {A B : Finset V}
    (m m' : ↥G.edgeFinset → ℕ)
    (hweight_nonneg :
      0 ≤ Sharpness.weight G β J (Sharpness.ofEdgeFun G m))
    (I : EdgeCopySourceSectorInjection G A B m m')
    (h : ∀ e, m e = m' e) :
    edgeCopySourcePairEmptyCollapsedTerm G β J A m ≤
      edgeCopySourcePairEmptyCollapsedTerm G β J B m' :=
  edgeCopySourcePairEmptyCollapsedTerm_le_of_sourceSectorInjection_of_weight_le
    G β J m m' hweight_nonneg I
    (weight_ofEdgeFun_le_of_edge_multiplicity_eq G β J h)


theorem edgeCopySourcePairEmptyCollapsedTerm_le_of_sourceSectorImageEmbedding_of_edge_multiplicity_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) {A B : Finset V}
    (m m' : ↥G.edgeFinset → ℕ)
    (hweight_nonneg :
      0 ≤ Sharpness.weight G β J (Sharpness.ofEdgeFun G m))
    (I : EdgeCopySourceSectorImageEmbedding G A B m m')
    (h : ∀ e, m e = m' e) :
    edgeCopySourcePairEmptyCollapsedTerm G β J A m ≤
      edgeCopySourcePairEmptyCollapsedTerm G β J B m' :=
  edgeCopySourcePairEmptyCollapsedTerm_le_of_sourceSectorImageEmbedding_of_weight_le
    G β J m m' hweight_nonneg I
    (weight_ofEdgeFun_le_of_edge_multiplicity_eq G β J h)


theorem edgeCopySourcePairEmptyCollapsedTerm_le_of_sourceSectorInjection_of_edge_equiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) {A B : Finset V}
    (m m' : ↥G.edgeFinset → ℕ)
    (hweight_nonneg :
      0 ≤ Sharpness.weight G β J (Sharpness.ofEdgeFun G m))
    (I : EdgeCopySourceSectorInjection G A B m m')
    (σ : ↥G.edgeFinset ≃ ↥G.edgeFinset)
    (hJ : ∀ e, J (σ e).1 = J e.1)
    (hm : ∀ e, m' (σ e) = m e) :
    edgeCopySourcePairEmptyCollapsedTerm G β J A m ≤
      edgeCopySourcePairEmptyCollapsedTerm G β J B m' :=
  edgeCopySourcePairEmptyCollapsedTerm_le_of_sourceSectorInjection_of_weight_le
    G β J m m' hweight_nonneg I
    (weight_ofEdgeFun_le_of_edge_equiv G β J σ hJ hm)


theorem edgeCopySourcePairEmptyCollapsedTerm_le_of_sourceSectorImageEmbedding_of_edge_equiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) {A B : Finset V}
    (m m' : ↥G.edgeFinset → ℕ)
    (hweight_nonneg :
      0 ≤ Sharpness.weight G β J (Sharpness.ofEdgeFun G m))
    (I : EdgeCopySourceSectorImageEmbedding G A B m m')
    (σ : ↥G.edgeFinset ≃ ↥G.edgeFinset)
    (hJ : ∀ e, J (σ e).1 = J e.1)
    (hm : ∀ e, m' (σ e) = m e) :
    edgeCopySourcePairEmptyCollapsedTerm G β J A m ≤
      edgeCopySourcePairEmptyCollapsedTerm G β J B m' :=
  edgeCopySourcePairEmptyCollapsedTerm_le_of_sourceSectorImageEmbedding_of_weight_le
    G β J m m' hweight_nonneg I
    (weight_ofEdgeFun_le_of_edge_equiv G β J σ hJ hm)


theorem edgeCopySourcePairEmptyCollapsedTerm_le_of_sourceSectorInjection_of_edge_equiv_homogeneous
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) {A B : Finset V}
    (m m' : ↥G.edgeFinset → ℕ)
    (hweight_nonneg :
      0 ≤ Sharpness.weight G β (fun _ => 1) (Sharpness.ofEdgeFun G m))
    (I : EdgeCopySourceSectorInjection G A B m m')
    (σ : ↥G.edgeFinset ≃ ↥G.edgeFinset)
    (hm : ∀ e, m' (σ e) = m e) :
    edgeCopySourcePairEmptyCollapsedTerm G β (fun _ => 1) A m ≤
      edgeCopySourcePairEmptyCollapsedTerm G β (fun _ => 1) B m' :=
  edgeCopySourcePairEmptyCollapsedTerm_le_of_sourceSectorInjection_of_weight_le
    G β (fun _ => 1) m m' hweight_nonneg I
    (weight_ofEdgeFun_le_of_edge_equiv_homogeneous G β σ hm)


theorem edgeCopySourcePairEmptyCollapsedTerm_le_of_sourceSectorImageEmbedding_of_edge_equiv_homogeneous
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) {A B : Finset V}
    (m m' : ↥G.edgeFinset → ℕ)
    (hweight_nonneg :
      0 ≤ Sharpness.weight G β (fun _ => 1) (Sharpness.ofEdgeFun G m))
    (I : EdgeCopySourceSectorImageEmbedding G A B m m')
    (σ : ↥G.edgeFinset ≃ ↥G.edgeFinset)
    (hm : ∀ e, m' (σ e) = m e) :
    edgeCopySourcePairEmptyCollapsedTerm G β (fun _ => 1) A m ≤
      edgeCopySourcePairEmptyCollapsedTerm G β (fun _ => 1) B m' :=
  edgeCopySourcePairEmptyCollapsedTerm_le_of_sourceSectorImageEmbedding_of_weight_le
    G β (fun _ => 1) m m' hweight_nonneg I
    (weight_ofEdgeFun_le_of_edge_equiv_homogeneous G β σ hm)


theorem edgeCopySourcePairEmptyCollapsedTerm_le_of_edgeEquivVertexEquiv_homogeneous
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) {A B : Finset V}
    (m m' : ↥G.edgeFinset → ℕ)
    (hβ : 0 ≤ β)
    (φ : V ≃ V)
    (σ : ↥G.edgeFinset ≃ ↥G.edgeFinset)
    (hm : ∀ e, m' (σ e) = m e)
    (hends : ∀ e, (σ e).1 = Sym2.map φ e.1)
    (hAB : A.map φ.toEmbedding = B) :
    edgeCopySourcePairEmptyCollapsedTerm G β (fun _ => 1) A m ≤
      edgeCopySourcePairEmptyCollapsedTerm G β (fun _ => 1) B m' :=
  edgeCopySourcePairEmptyCollapsedTerm_le_of_sourceSectorImageEmbedding_of_edge_equiv_homogeneous
    G β m m'
    (weight_ofEdgeFun_nonneg G β (fun _ => 1) hβ
      (by intro e; norm_num) m)
    (EdgeCopySourceSectorImageEmbedding.ofEdgeEquivVertexEquiv
      φ σ hm hends hAB)
    σ hm


theorem doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm_le_of_multiplicity_le_of_weight_le
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (m m' : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hβ : 0 ≤ β)
    (hmult :
      doubledBoxOriginToInnerEndpointEdgeCopyCollapsedMultiplicity n v m ≤
        doubledBoxOriginToInnerEndpointEdgeCopyCollapsedMultiplicity n w m')
    (hweight :
      Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m) ≤
        Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m')) :
    doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n v m ≤
      doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w m' :=
  edgeCopySourcePairEmptyCollapsedTerm_le_of_multiplicity_le_of_weight_le
    (FK.boxGraph 3 (2 * n)) β (fun _ => 1) m m'
    (weight_ofEdgeFun_nonneg (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      hβ (by intro e; norm_num) m)
    hmult hweight


theorem doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm_le_of_sourceSectorInjection_of_weight_le
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (m m' : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hβ : 0 ≤ β)
    (I :
      EdgeCopySourceSectorInjection (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (doubledBoxOriginToInnerEndpointSource n w) m m')
    (hweight :
      Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m) ≤
        Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m')) :
    doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n v m ≤
      doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w m' :=
  edgeCopySourcePairEmptyCollapsedTerm_le_of_sourceSectorInjection_of_weight_le
    (FK.boxGraph 3 (2 * n)) β (fun _ => 1) m m'
    (weight_ofEdgeFun_nonneg (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      hβ (by intro e; norm_num) m)
    I hweight


theorem doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm_le_of_sourceSectorImageEmbedding_of_weight_le
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (m m' : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hβ : 0 ≤ β)
    (I :
      EdgeCopySourceSectorImageEmbedding (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (doubledBoxOriginToInnerEndpointSource n w) m m')
    (hweight :
      Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m) ≤
        Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m')) :
    doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n v m ≤
      doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w m' :=
  edgeCopySourcePairEmptyCollapsedTerm_le_of_sourceSectorImageEmbedding_of_weight_le
    (FK.boxGraph 3 (2 * n)) β (fun _ => 1) m m'
    (weight_ofEdgeFun_nonneg (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      hβ (by intro e; norm_num) m)
    I hweight


theorem doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm_le_of_sourceSectorInsertEmbedding_of_weight_le
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (m m' : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hβ : 0 ≤ β)
    (I :
      EdgeCopySourceSectorInsertEmbedding (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (doubledBoxOriginToInnerEndpointSource n w) m m')
    (hweight :
      Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m) ≤
        Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m')) :
    doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n v m ≤
      doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w m' :=
  edgeCopySourcePairEmptyCollapsedTerm_le_of_sourceSectorInsertEmbedding_of_weight_le
    (FK.boxGraph 3 (2 * n)) β (fun _ => 1) m m'
    (weight_ofEdgeFun_nonneg (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      hβ (by intro e; norm_num) m)
    I hweight


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm_le_edgeIncrement_count_mul
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hβ : 0 ≤ β)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n v m ≤
      (((m e0 + 1 : ℕ) : ℝ)) *
        doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w
          (Function.update m e0 (m e0 + 1)) := by
  let G := FK.boxGraph 3 (2 * n)
  let A := doubledBoxOriginToInnerEndpointSource n v
  let B := doubledBoxOriginToInnerEndpointSource n w
  let m' := Function.update m e0 (m e0 + 1)
  let c : ℝ := ((m e0 + 1 : ℕ) : ℝ)
  let wSource :=
    Sharpness.weight G β (fun _ => 1) (Sharpness.ofEdgeFun G m)
  let wTarget :=
    Sharpness.weight G β (fun _ => 1) (Sharpness.ofEdgeFun G m')
  let multSource := edgeCopySourcePairEmptyCollapsedMultiplicity G A m
  let multTarget := edgeCopySourcePairEmptyCollapsedMultiplicity G B m'
  have I :
      EdgeCopySourceSectorInsertEmbedding G A B m m' :=
    EdgeCopySourceSectorInsertEmbedding.doubledBoxOriginToInnerEndpoint_edgeIncrement
      (n := n) (v := v) (w := w) m e0 hedge hov how hvw
  have hmult : multSource ≤ multTarget :=
    edgeCopySourcePairEmptyCollapsedMultiplicity_le_of_sourceSectorInsertEmbedding
      G I
  have htarget_nonneg : 0 ≤ wTarget :=
    weight_ofEdgeFun_nonneg G β (fun _ => 1) hβ (by intro e; norm_num) m'
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hweight :
      c * wTarget = β * wSource := by
    dsimp [c, wSource, wTarget, m', G]
    simpa using weight_ofEdgeFun_increment (FK.boxGraph 3 (2 * n)) β
      (fun _ => 1) m e0
  have hfactor_nonneg : 0 ≤ β * wSource := by
    rw [← hweight]
    exact mul_nonneg hc_nonneg htarget_nonneg
  rw [doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm,
    doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm,
    edgeCopySourcePairEmptyCollapsedTerm_eq_multiplicity_mul_weight,
    edgeCopySourcePairEmptyCollapsedTerm_eq_multiplicity_mul_weight]
  change β * (multSource * wSource) ≤ c * (multTarget * wTarget)
  calc
    β * (multSource * wSource) =
        multSource * (β * wSource) := by ring
    _ ≤ multTarget * (β * wSource) :=
        mul_le_mul_of_nonneg_right hmult hfactor_nonneg
    _ = multTarget * (c * wTarget) := by rw [hweight]
    _ = c * (multTarget * wTarget) := by ring


theorem doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm_le_of_sourceSectorInjection_of_ofEdgeFun_eq
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (m m' : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hβ : 0 ≤ β)
    (I :
      EdgeCopySourceSectorInjection (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (doubledBoxOriginToInnerEndpointSource n w) m m')
    (h :
      Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m =
        Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m') :
    doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n v m ≤
      doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w m' :=
  doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm_le_of_sourceSectorInjection_of_weight_le
    m m' hβ I
    (weight_ofEdgeFun_le_of_ofEdgeFun_eq
      (FK.boxGraph 3 (2 * n)) β (fun _ => 1) h)


theorem doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm_le_of_sourceSectorImageEmbedding_of_ofEdgeFun_eq
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (m m' : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hβ : 0 ≤ β)
    (I :
      EdgeCopySourceSectorImageEmbedding (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (doubledBoxOriginToInnerEndpointSource n w) m m')
    (h :
      Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m =
        Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m') :
    doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n v m ≤
      doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w m' :=
  doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm_le_of_sourceSectorImageEmbedding_of_weight_le
    m m' hβ I
    (weight_ofEdgeFun_le_of_ofEdgeFun_eq
      (FK.boxGraph 3 (2 * n)) β (fun _ => 1) h)


theorem doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm_le_of_sourceSectorInsertEmbedding_of_ofEdgeFun_eq
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (m m' : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hβ : 0 ≤ β)
    (I :
      EdgeCopySourceSectorInsertEmbedding (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (doubledBoxOriginToInnerEndpointSource n w) m m')
    (h :
      Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m =
        Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m') :
    doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n v m ≤
      doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w m' :=
  doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm_le_of_sourceSectorInsertEmbedding_of_weight_le
    m m' hβ I
    (weight_ofEdgeFun_le_of_ofEdgeFun_eq
      (FK.boxGraph 3 (2 * n)) β (fun _ => 1) h)


theorem doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm_le_of_sourceSectorInjection_of_edge_multiplicity_eq
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (m m' : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hβ : 0 ≤ β)
    (I :
      EdgeCopySourceSectorInjection (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (doubledBoxOriginToInnerEndpointSource n w) m m')
    (h : ∀ e, m e = m' e) :
    doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n v m ≤
      doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w m' :=
  doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm_le_of_sourceSectorInjection_of_weight_le
    m m' hβ I
    (weight_ofEdgeFun_le_of_edge_multiplicity_eq
      (FK.boxGraph 3 (2 * n)) β (fun _ => 1) h)


theorem doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm_le_of_sourceSectorImageEmbedding_of_edge_multiplicity_eq
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (m m' : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hβ : 0 ≤ β)
    (I :
      EdgeCopySourceSectorImageEmbedding (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (doubledBoxOriginToInnerEndpointSource n w) m m')
    (h : ∀ e, m e = m' e) :
    doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n v m ≤
      doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w m' :=
  doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm_le_of_sourceSectorImageEmbedding_of_weight_le
    m m' hβ I
    (weight_ofEdgeFun_le_of_edge_multiplicity_eq
      (FK.boxGraph 3 (2 * n)) β (fun _ => 1) h)


theorem doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm_le_of_sourceSectorInjection_of_edge_equiv
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (m m' : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hβ : 0 ≤ β)
    (I :
      EdgeCopySourceSectorInjection (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (doubledBoxOriginToInnerEndpointSource n w) m m')
    (σ :
      ↥(FK.boxGraph 3 (2 * n)).edgeFinset ≃
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hm : ∀ e, m' (σ e) = m e) :
    doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n v m ≤
      doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w m' :=
  doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm_le_of_sourceSectorInjection_of_weight_le
    m m' hβ I
    (weight_ofEdgeFun_le_of_edge_equiv_homogeneous
      (FK.boxGraph 3 (2 * n)) β σ hm)


theorem doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm_le_of_sourceSectorImageEmbedding_of_edge_equiv
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (m m' : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hβ : 0 ≤ β)
    (I :
      EdgeCopySourceSectorImageEmbedding (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (doubledBoxOriginToInnerEndpointSource n w) m m')
    (σ :
      ↥(FK.boxGraph 3 (2 * n)).edgeFinset ≃
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hm : ∀ e, m' (σ e) = m e) :
    doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n v m ≤
      doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w m' :=
  doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm_le_of_sourceSectorImageEmbedding_of_weight_le
    m m' hβ I
    (weight_ofEdgeFun_le_of_edge_equiv_homogeneous
      (FK.boxGraph 3 (2 * n)) β σ hm)


theorem doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm_le_of_edgeEquivVertexEquiv
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (m m' : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hβ : 0 ≤ β)
    (φ : FK.boxVerts 3 (2 * n) ≃ FK.boxVerts 3 (2 * n))
    (σ :
      ↥(FK.boxGraph 3 (2 * n)).edgeFinset ≃
        ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hm : ∀ e, m' (σ e) = m e)
    (hends : ∀ e, (σ e).1 = Sym2.map φ e.1)
    (hsrc :
      (doubledBoxOriginToInnerEndpointSource n v).map φ.toEmbedding =
        doubledBoxOriginToInnerEndpointSource n w) :
    doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n v m ≤
      doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w m' :=
  edgeCopySourcePairEmptyCollapsedTerm_le_of_edgeEquivVertexEquiv_homogeneous
    (FK.boxGraph 3 (2 * n)) β m m' hβ φ σ hm hends hsrc


theorem doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm_eq_zero_of_not_fullSource
    {β : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hsrc :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
        (Finset.univ :
          Finset (Sharpness.FluxEdgeCopy.Copy
            (FK.boxGraph 3 (2 * n)) m)) ≠
          doubledBoxOriginToInnerEndpointSource n v) :
    doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n v m = 0 :=
  edgeCopySourcePairEmptyCollapsedTerm_eq_zero_of_not_fullSource
    (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
    (doubledBoxOriginToInnerEndpointSource n v) m hsrc


theorem finset_mul_sum_le_sum_image_of_injOn
    {α γ : Type*} [DecidableEq γ]
    (s : Finset α) (φ : α → γ)
    (hφ : ∀ x ∈ s, ∀ y ∈ s, φ x = φ y → x = y)
    (a : ℝ) (c : γ → ℝ) (f : α → ℝ) (g : γ → ℝ)
    (hpoint : ∀ x ∈ s, a * f x ≤ c (φ x) * g (φ x)) :
    a * (∑ x ∈ s, f x) ≤ ∑ y ∈ s.image φ, c y * g y := by
  rw [Finset.mul_sum]
  calc
    (∑ x ∈ s, a * f x) ≤ ∑ x ∈ s, c (φ x) * g (φ x) := by
      exact Finset.sum_le_sum fun x hx => hpoint x hx
    _ = ∑ y ∈ s.image φ, c y * g y := by
      rw [Finset.sum_image]
      intro x hx y hy hxy
      exact hφ x hx y hy hxy

set_option linter.style.longLine false in


theorem finset_sum_route_le_tsum_of_injOn_nonneg
    {α γ : Type*}
    (s : Finset α) (route : α → γ) (capacity : γ → ℝ)
    (hinj : Set.InjOn route s)
    (hsummable : Summable capacity)
    (hnonneg : ∀ y, 0 ≤ capacity y) :
    (∑ a ∈ s, capacity (route a)) ≤ ∑' y, capacity y := by
  classical
  calc
    (∑ a ∈ s, capacity (route a)) =
        ∑ y ∈ s.image route, capacity y := by
      rw [Finset.sum_image]
      intro a ha b hb hab
      exact hinj ha hb hab
    _ ≤ ∑' y, capacity y :=
      hsummable.sum_le_tsum (s.image route) (fun y _hy => hnonneg y)

set_option linter.style.longLine false in


theorem edgeCopySourcePairSummand_finset_sum_route_le_sourcePairSum_of_injOn
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβ : 0 ≤ β) (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (A B : Finset V)
    (s : Finset (↥G.edgeFinset → ℕ))
    (route : (↥G.edgeFinset → ℕ) → (↥G.edgeFinset → ℕ))
    (hinj : Set.InjOn route s) :
    (∑ m ∈ s, edgeCopySourcePairSummand G β J A B (route m)) ≤
      Sharpness.sourcePairSum G β J A B := by
  calc
    (∑ m ∈ s, edgeCopySourcePairSummand G β J A B (route m)) ≤
        ∑' m : ↥G.edgeFinset → ℕ, edgeCopySourcePairSummand G β J A B m :=
      finset_sum_route_le_tsum_of_injOn_nonneg s route
        (fun m => edgeCopySourcePairSummand G β J A B m) hinj
        (edgeCopySourcePairSummand_summable G β J A B)
        (fun m => edgeCopySourcePairSummand_nonneg G β J A B m hβ hJ)
    _ = Sharpness.sourcePairSum G β J A B := by
      rw [sourcePairSum_eq_edgeCopySourcePairSum]
      rfl


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm_finset_sum_le_edgeIncrement_image_count_mul
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hβ : 0 ≤ β)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    β * (∑ m ∈ Ω,
        doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n v m) ≤
      ∑ m' ∈ Ω.image
          (fun m => Function.update m e0 (m e0 + 1)),
        ((m' e0 : ℕ) : ℝ) *
          doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w m' := by
  refine
    finset_mul_sum_le_sum_image_of_injOn Ω
      (fun m => Function.update m e0 (m e0 + 1))
      ?_ β
      (fun m' => ((m' e0 : ℕ) : ℝ))
      (fun m => doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n v m)
      (fun m' => doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w m')
      ?_
  · intro x _hx y _hy hxy
    exact edgeMultiplicityIncrement_injective e0 hxy
  · intro m _hm
    simpa [Function.update_self] using
      beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm_le_edgeIncrement_count_mul
        (n := n) (v := v) (w := w) m e0 hβ hedge hov how hvw

set_option linter.style.longLine false in


theorem doubledBox_edgeIncrement_image_count_mul_targetTerm_finset_sum_le_beta_mul_preimage_edgeMultiplicitySucc_branchSourcePairSummand_sum
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hβ : 0 ≤ β)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    (∑ m' ∈ Ω.image (fun m => Function.update m e0 (m e0 + 1)),
      ((m' e0 : ℕ) : ℝ) *
        doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w m') ≤
      β *
        ∑ m ∈ Ω,
          (((m e0 + 1 : ℕ) : ℝ) *
            edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n v)
              (∅ : Finset (FK.boxVerts 3 (2 * n))) m +
            ((m e0 + 1 : ℕ) : ℝ) *
            edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w) m) := by
  classical
  let φ : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
      (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :=
    fun m => Function.update m e0 (m e0 + 1)
  calc
    (∑ m' ∈ Ω.image (fun m => Function.update m e0 (m e0 + 1)),
      ((m' e0 : ℕ) : ℝ) *
        doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w m') =
        ∑ m ∈ Ω,
          ((φ m e0 : ℕ) : ℝ) *
            doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w (φ m) := by
      rw [Finset.sum_image]
      intro x hx y hy hxy
      exact edgeMultiplicityIncrement_injective e0 hxy
    _ ≤ ∑ m ∈ Ω,
          β *
            ((((m e0 + 1 : ℕ) : ℝ) *
              edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
                (fun _ => 1)
                (doubledBoxOriginToInnerEndpointSource n v)
                (∅ : Finset (FK.boxVerts 3 (2 * n))) m) +
              (((m e0 + 1 : ℕ) : ℝ) *
              edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
                (fun _ => 1)
                (doubledBoxOriginToInnerEndpointSource n w)
                (doubledBoxInnerPairSource n v w) m)) := by
      refine Finset.sum_le_sum ?_
      intro m _hm
      have hpoint :=
        doubledBox_edge_count_mul_targetTerm_le_beta_mul_edgeMultiplicityFixedDecrementBranchSourcePairSummands
          (n := n) (v := v) (w := w) hβ (φ m) e0 hedge hov how hvw
      simpa [φ, Function.update_self, edgeMultiplicityIncrement_decrement_eq]
        using hpoint
    _ = β *
        ∑ m ∈ Ω,
          (((m e0 + 1 : ℕ) : ℝ) *
            edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n v)
              (∅ : Finset (FK.boxVerts 3 (2 * n))) m +
            ((m e0 + 1 : ℕ) : ℝ) *
            edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w) m) := by
      rw [← Finset.mul_sum]

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm_finset_sum_le_beta_mul_edgeMultiplicitySucc_branchSourcePairSummand_sum
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hβ : 0 ≤ β)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    β * (∑ m ∈ Ω,
        doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n v m) ≤
      β *
        ∑ m ∈ Ω,
          (((m e0 + 1 : ℕ) : ℝ) *
            edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n v)
              (∅ : Finset (FK.boxVerts 3 (2 * n))) m +
            ((m e0 + 1 : ℕ) : ℝ) *
            edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w) m) :=
  (beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm_finset_sum_le_edgeIncrement_image_count_mul
    (n := n) (v := v) (w := w) Ω e0 hβ hedge hov how hvw).trans
    (doubledBox_edgeIncrement_image_count_mul_targetTerm_finset_sum_le_beta_mul_preimage_edgeMultiplicitySucc_branchSourcePairSummand_sum
      (n := n) (v := v) (w := w) Ω e0 hβ hedge hov how hvw)

end Exact3D
end StatMech

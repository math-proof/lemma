/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousParityAvoidance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.NonnegativeCurrentConditionalPMF.Part5
import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxEvenLimit.Part6
import Def.StatisticalMechanics.Code.FrontierB.InhomogeneousParityAvoidance
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem sinh_eq_cosh_mul_tanh (x : ℝ) :
    Real.sinh x = Real.cosh x * Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp

theorem inhomogeneousParityFiberMass_eq_cosh_mul_highTemp
    (beta : ℝ) (J : Sym2 V → ℝ)
    (H : Finset (Sym2 V)) (hH : H ⊆ G.edgeFinset) :
    inhomogeneousParityFiberMass G (fun e => beta * J e) H =
      (∏ e ∈ G.edgeFinset, Real.cosh (beta * J e)) *
        highTempSubgraphWeight beta J H := by
  unfold inhomogeneousParityFiberMass highTempSubgraphWeight
  rw [Finset.prod_ite]
  have hprod_mem (f : Sym2 V → ℝ) :
      (∏ x : G.edgeFinset with x.1 ∈ H, f x.1) = ∏ e ∈ H, f e := by
    symm
    apply Finset.prod_bij (fun e he => ⟨e, hH he⟩)
    · intro e he
      simp [he]
    · intro e₁ h₁ e₂ h₂ heq
      exact congrArg Subtype.val heq
    · intro x hx
      refine ⟨x.1, ?_, ?_⟩
      · simpa using hx
      · apply Subtype.ext
        rfl
    · simp
  have hprod_not (f : Sym2 V → ℝ) :
      (∏ x : G.edgeFinset with x.1 ∉ H, f x.1) =
        ∏ e ∈ G.edgeFinset \ H, f e := by
    symm
    apply Finset.prod_bij (fun e he => ⟨e, (Finset.mem_sdiff.mp he).1⟩)
    · intro e he
      simp [(Finset.mem_sdiff.mp he).2]
    · intro e₁ h₁ e₂ h₂ heq
      exact congrArg Subtype.val heq
    · intro x hx
      refine ⟨x.1, ?_, ?_⟩
      · exact Finset.mem_sdiff.mpr ⟨x.2, by simpa using hx⟩
      · apply Subtype.ext
        rfl
    · simp
  rw [show (∏ x : G.edgeFinset with x.1 ∈ H,
      Real.sinh ((fun e => beta * J e) x.1)) =
        ∏ e ∈ H, Real.sinh (beta * J e) from
      hprod_mem (fun e => Real.sinh (beta * J e))]
  rw [show (∏ x : G.edgeFinset with x.1 ∉ H,
      Real.cosh ((fun e => beta * J e) x.1)) =
        ∏ e ∈ G.edgeFinset \ H, Real.cosh (beta * J e) from
      hprod_not (fun e => Real.cosh (beta * J e))]
  simp_rw [sinh_eq_cosh_mul_tanh]
  rw [Finset.prod_mul_distrib]
  calc
    (∏ e ∈ H, Real.cosh (beta * J e)) *
          (∏ e ∈ H, Real.tanh (beta * J e)) *
          ∏ e ∈ G.edgeFinset \ H, Real.cosh (beta * J e) =
        ((∏ e ∈ G.edgeFinset \ H, Real.cosh (beta * J e)) *
          ∏ e ∈ H, Real.cosh (beta * J e)) *
            ∏ e ∈ H, Real.tanh (beta * J e) := by ring
    _ = _ := by rw [Finset.prod_sdiff hH]

theorem partitionJ_eq_cosh_mul_inhomogeneousParityPartition
    (beta : ℝ) (J : Sym2 V → ℝ) :
    partitionJ G beta J =
      (2 : ℝ) ^ Fintype.card V *
        (∏ e ∈ G.edgeFinset, Real.cosh (beta * J e)) *
          inhomogeneousParityPartition G beta J := by
  unfold partitionJ inhomogeneousParityPartition
  rw [show (∑ s : ConfigSpace V, boltzmannJ G beta J s) =
      ∑ s : ConfigSpace V, spinProd (∅ : Finset V) s *
        boltzmannJ G beta J s by simp]
  rw [spinProd_boltzmannJ_high_temp_expansion G beta J ∅]
  simp only [hasOddBoundary_empty]

theorem currentSum_eq_cosh_mul_inhomogeneousParityPartition
    (beta : ℝ) (J : Sym2 V → ℝ) :
    currentSum G beta J ∅ =
      (∏ e ∈ G.edgeFinset, Real.cosh (beta * J e)) *
        inhomogeneousParityPartition G beta J := by
  have h := partitionJ_eq_currentSum G beta J
  rw [partitionJ_eq_cosh_mul_inhomogeneousParityPartition] at h
  rw [mul_assoc] at h
  have htwo : (2 : ℝ) ^ Fintype.card V ≠ 0 := by positivity
  exact (mul_left_cancel₀ htwo h).symm

theorem inhomogeneousParityPartition_pos
    (beta : ℝ) (hbeta : 0 ≤ beta) (J : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) :
    0 < inhomogeneousParityPartition G beta J := by
  unfold inhomogeneousParityPartition
  have hempty : (∅ : Finset (Sym2 V)) ∈
      G.edgeFinset.powerset.filter IsEvenSubgraph := by
    simp [IsEvenSubgraph, incCount]
  have hnonneg : ∀ H ∈ G.edgeFinset.powerset.filter IsEvenSubgraph,
      0 ≤ highTempSubgraphWeight beta J H := by
    intro H hH
    unfold highTempSubgraphWeight
    exact Finset.prod_nonneg fun e he =>
      tanh_nonneg_of_nonneg (mul_nonneg hbeta (hJ e))
  exact lt_of_lt_of_le Real.zero_lt_one (by
    simpa [highTempSubgraphWeight] using
      Finset.single_le_sum hnonneg hempty)

theorem sourcelessNonnegativeParityPMF_apply_eq_highTemp
    (beta : ℝ) (hbeta : 0 < beta) (J : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (H : Finset (Sym2 V)) :
    sourcelessNonnegativeParityPMF G beta J hbeta.le hJ H =
      if hvalid : H ⊆ G.edgeFinset ∧ IsEvenSubgraph H then
        ENNReal.ofReal (highTempSubgraphWeight beta J H) *
          (ENNReal.ofReal (inhomogeneousParityPartition G beta J))⁻¹
      else 0 := by
  rw [sourcelessNonnegativeParityPMF_apply G beta hbeta J hJ H]
  by_cases hvalid : H ⊆ G.edgeFinset ∧ IsEvenSubgraph H
  · rw [dif_pos hvalid, dif_pos hvalid,
      inhomogeneousParityFiberMass_eq_cosh_mul_highTemp G beta J H hvalid.1,
      currentSum_eq_cosh_mul_inhomogeneousParityPartition G beta J]
    let c : ENNReal := ENNReal.ofReal
      (∏ e ∈ G.edgeFinset, Real.cosh (beta * J e))
    let t : ENNReal := ENNReal.ofReal (highTempSubgraphWeight beta J H)
    let p : ENNReal := ENNReal.ofReal
      (inhomogeneousParityPartition G beta J)
    have hcReal : 0 ≤ ∏ e ∈ G.edgeFinset,
        Real.cosh (beta * J e) := Finset.prod_nonneg fun e _ =>
      (Real.cosh_pos _).le
    have htReal : 0 ≤ highTempSubgraphWeight beta J H := by
      unfold highTempSubgraphWeight
      exact Finset.prod_nonneg fun e _ =>
        tanh_nonneg_of_nonneg (mul_nonneg hbeta.le (hJ e))
    rw [ENNReal.ofReal_mul hcReal, ENNReal.ofReal_mul hcReal]
    have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have hcTop : c ≠ ⊤ := ENNReal.ofReal_ne_top
    change c * t * (c * p)⁻¹ = t * p⁻¹
    rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hcTop)]
    calc
      c * t * (c⁻¹ * p⁻¹) = (c * c⁻¹) * (t * p⁻¹) := by
        ac_rfl
      _ = t * p⁻¹ := by rw [ENNReal.mul_inv_cancel hc0 hcTop, one_mul]
  · rw [dif_neg hvalid, dif_neg hvalid]

theorem sourcelessNonnegativeParityMeasure_avoid
    (beta : ℝ) (hbeta : 0 < beta) (J : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (F : Finset (Sym2 V)) :
    (sourcelessNonnegativeParityPMF G beta J hbeta.le hJ).toMeasure
        {H | Disjoint H F} =
      ENNReal.ofReal
        (inhomogeneousParityAvoidSum G beta J F /
          inhomogeneousParityPartition G beta J) := by
  classical
  rw [PMF.toMeasure_apply_eq_tsum, tsum_fintype,
    ENNReal.ofReal_div_of_pos
      (inhomogeneousParityPartition_pos G beta hbeta.le J hJ)]
  let p := ENNReal.ofReal (inhomogeneousParityPartition G beta J)
  let r : Finset (Sym2 V) → ℝ := fun H =>
    if H ⊆ G.edgeFinset ∧ IsEvenSubgraph H ∧ Disjoint H F then
      highTempSubgraphWeight beta J H else 0
  have hrnonneg : ∀ H, 0 ≤ r H := by
    intro H
    simp only [r]
    split
    · unfold highTempSubgraphWeight
      exact Finset.prod_nonneg fun e _ =>
        tanh_nonneg_of_nonneg (mul_nonneg hbeta.le (hJ e))
    · exact le_rfl
  have hrsum : (∑ H : Finset (Sym2 V), r H) =
      inhomogeneousParityAvoidSum G beta J F := by
    unfold inhomogeneousParityAvoidSum
    rw [Finset.sum_filter]
    symm
    apply Finset.sum_subset_zero_on_sdiff (Finset.subset_univ _)
    · intro H hgap
      have hnot : H ∉ G.edgeFinset.powerset := (Finset.mem_sdiff.mp hgap).2
      have hsub : ¬H ⊆ G.edgeFinset := by simpa using hnot
      simp [r, hsub]
    · intro H hpow
      have hsub : H ⊆ G.edgeFinset := Finset.mem_powerset.mp hpow
      by_cases heven : IsEvenSubgraph H <;>
        by_cases hd : Disjoint H F <;> simp [r, hsub, heven, hd]
  have hnum :
      (∑ H : Finset (Sym2 V),
        if Disjoint H F ∧ H ⊆ G.edgeFinset ∧ IsEvenSubgraph H then
          ENNReal.ofReal (highTempSubgraphWeight beta J H) else 0) =
        ENNReal.ofReal (inhomogeneousParityAvoidSum G beta J F) := by
    rw [← hrsum, ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro H hH
      by_cases hs : H ⊆ G.edgeFinset <;>
        by_cases he : IsEvenSubgraph H <;>
          by_cases hd : Disjoint H F <;> simp [r, hs, he, hd]
    · intro H hH
      exact hrnonneg H
  calc
    (∑ H : Finset (Sym2 V),
        {H | Disjoint H F}.indicator
          (sourcelessNonnegativeParityPMF G beta J hbeta.le hJ) H) =
      ∑ H : Finset (Sym2 V),
        (if Disjoint H F ∧ H ⊆ G.edgeFinset ∧ IsEvenSubgraph H then
          ENNReal.ofReal (highTempSubgraphWeight beta J H) else 0) * p⁻¹ := by
      apply Finset.sum_congr rfl
      intro H hH
      by_cases hd : Disjoint H F
      · rw [Set.indicator_of_mem hd,
          sourcelessNonnegativeParityPMF_apply_eq_highTemp
            G beta hbeta J hJ H]
        by_cases hv : H ⊆ G.edgeFinset ∧ IsEvenSubgraph H
        · simp [hd, hv, p]
        · simp [hd, hv]
      · rw [Set.indicator_of_notMem hd]
        simp [hd]
    _ = (∑ H : Finset (Sym2 V),
        if Disjoint H F ∧ H ⊆ G.edgeFinset ∧ IsEvenSubgraph H then
          ENNReal.ofReal (highTempSubgraphWeight beta J H) else 0) * p⁻¹ := by
      rw [Finset.sum_mul]
    _ = ENNReal.ofReal (inhomogeneousParityAvoidSum G beta J F) * p⁻¹ := by
      rw [hnum]


end StatMech.FrontierB

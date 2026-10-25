/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.PBiasedConvexity.Part2
import Theorem.StatisticalMechanics.Code.Probability.KKLpBiased.Part2
import Theorem.StatisticalMechanics.Code.Probability.RhoOptimiseClose2
import Def.StatisticalMechanics.Code.Probability.PBiasedTensorize.Part9
open scoped BigOperators
open Finset
open Real

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem ptn_expect_reindex {κ : Type*} [Fintype κ] [DecidableEq κ] (σ : κ ≃ ι) (p : ℝ)
    (f : ConfigSpace ι → ℝ) :
    OSSS.expect (OSSS.bernoulliWeight p) (ptn_reindex σ f)
      = OSSS.expect (OSSS.bernoulliWeight p) f := by
  unfold OSSS.expect ptn_reindex
  symm
  apply Fintype.sum_equiv (ptn_cubeEquiv σ)
  intro x
  unfold ptn_cubeEquiv
  have hxj : ∀ j : κ, (σ.symm.arrowCongr (Equiv.refl Bool)) x j = x (σ j) := by
    intro j; simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp, Equiv.symm_symm,
      id_eq]
  congr 1
  · unfold OSSS.weight
    rw [← Equiv.prod_comp σ (fun i : ι => OSSS.bernoulliWeight p i (x i))]
    apply Finset.prod_congr rfl
    intro j _
    rw [hxj j]; simp only [OSSS.bernoulliWeight]
  · congr 1; funext i
    simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp, Equiv.symm_symm, id_eq,
      Equiv.apply_symm_apply]


theorem ptn_qnorm_reindex {κ : Type*} [Fintype κ] [DecidableEq κ] (σ : κ ≃ ι) (p q : ℝ)
    (f : ConfigSpace ι → ℝ) :
    ptn_qnorm p q (ptn_reindex σ f) = ptn_qnorm p q f := by
  unfold ptn_qnorm ptn_qnormPow
  congr 2
  rw [show (fun y => |ptn_reindex σ f y| ^ q) = ptn_reindex σ (fun x => |f x| ^ q) from rfl,
      ptn_expect_reindex]


theorem ptn_kop_reindex {κ : Type*} [Fintype κ] [DecidableEq κ] (σ : κ ≃ ι) (p ρ : ℝ)
    (f : ConfigSpace ι → ℝ) :
    ptn_kop p ρ (ptn_reindex σ f) = ptn_reindex σ (ptn_kop p ρ f) := by
  funext y
  unfold ptn_kop ptn_reindex ptn_kernel
  symm
  apply Fintype.sum_equiv (ptn_cubeEquiv σ)
  intro w
  unfold ptn_cubeEquiv
  simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp, Equiv.symm_symm, id_eq]
  congr 1
  · rw [← Equiv.prod_comp σ (fun i : ι => ptn_kbit p ρ (y (σ.symm i)) (w i))]
    apply Finset.prod_congr rfl
    intro j _
    simp only [Equiv.symm_apply_apply]
  · congr 1; funext i; rw [Equiv.apply_symm_apply]


theorem ptn_lowDegreeWeight {p ρ q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (h0 : 0 ≤ ρ)
    (h1 : ρ ≤ 1) (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (hρsq : ρ ^ 2 = (q - 1) * 4 * p * (1 - p))
    (f : ConfigSpace ι → ℝ) :
    (∑ S : Finset ι, (ρ ^ S.card) ^ 2 * (ptn_coeff p f S) ^ 2)
      ≤ (ptn_qnorm p q f) ^ 2 := by
  set σ : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm with hσ
  
  have hfin := ptn_lowDegreeWeight_fin hp0 hp1 h0 h1 hq1 hq2 hρsq (Fintype.card ι)
    (ptn_reindex σ f)
  
  have hL : (∑ S : Finset (Fin (Fintype.card ι)), (ρ ^ S.card) ^ 2 * (ptn_coeff p (ptn_reindex σ f) S) ^ 2)
      = ∑ S : Finset ι, (ρ ^ S.card) ^ 2 * (ptn_coeff p f S) ^ 2 := by
    rw [← ptn_noiseOp_l2sq hp0 hp1, ← ptn_noiseOp_l2sq hp0 hp1,
        ← ptn_kop_eq_noiseOp hp0 hp1, ← ptn_kop_eq_noiseOp hp0 hp1,
        ptn_kop_reindex σ p ρ f]
    rw [show (fun ω => (ptn_reindex σ (ptn_kop p ρ f) ω) ^ 2)
        = ptn_reindex σ (fun x => (ptn_kop p ρ f x) ^ 2) from rfl, ptn_expect_reindex]
  rw [hL, ptn_qnorm_reindex σ p q f] at hfin
  exact hfin


end StatMech.Probability

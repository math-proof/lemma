/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfefiniteenergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bfin2assemble
import Theorem.StatisticalMechanics.Code.Walls.bftfinetrif.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc67supervertex.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc62coarseclose.Part2
import Theorem.StatisticalMechanics.Code.Walls.bpeprobcount.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc120closure
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bfe_coarseCount_eq_fineCount (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ) :
    bc61_coarseTcount ω 0 R = (bfin2_trifSet_finite ω (R + 1)).toFinset.card := by
  classical
  unfold bc61_coarseTcount
  congr 1
  apply Finset.ext
  intro y
  rw [bc61_mem_coarseTrifFinset, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
    bc67_coarseTrif_is_G_n_trifurcation ω 0 y]
  have hb : (R + 1) - 1 = R := by omega
  rw [hb]
  unfold bft_FineTrif
  exact and_comm


theorem bfe_perConfig_count (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ) :
    bc61_coarseTcount ω 0 R ≤ boxSV_boundaryCard d (R + 1) := by
  rw [bfe_coarseCount_eq_fineCount ω R]
  calc (bfin2_trifSet_finite ω (R + 1)).toFinset.card
      ≤ (vertexBoundary_finite d (R + 1)).toFinset.card :=
        bfin2_count ω (R + 1) (Nat.succ_le_succ (Nat.zero_le R))
    _ = boxSV_boundaryCard d (R + 1) := rfl


theorem bfe_exp_eq (μ : Measure (ConfigSpace (Sym2 (Site d))))
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) (R : ℕ) :
    ((boxFinsetBK d R).card : ENNReal) * μ {ω | bc61_IsCoarseTrifurcation ω 0 0}
      = ∫⁻ ω, (bc61_coarseTcount ω 0 R : ENNReal) ∂μ :=
  bc62_coarse_expectation μ hinv 0 R


theorem bfe_expBound (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (R : ℕ) :
    ∫⁻ ω, (bc61_coarseTcount ω 0 R : ENNReal) ∂μ ≤ (boxSV_boundaryCard d (R + 1) : ENNReal) := by
  calc ∫⁻ ω, (bc61_coarseTcount ω 0 R : ENNReal) ∂μ
      ≤ ∫⁻ _ω, (boxSV_boundaryCard d (R + 1) : ENNReal) ∂μ := by
        apply lintegral_mono; intro ω; exact Nat.cast_le.mpr (bfe_perConfig_count ω R)
    _ = (boxSV_boundaryCard d (R + 1) : ENNReal) := by
        rw [lintegral_const, measure_univ, mul_one]


theorem bfe_boxCard (R : ℕ) : ((boxFinsetBK d R).card : ℝ) = (2 * (R : ℝ) + 1) ^ d := by
  unfold boxFinsetBK; rw [← boxSV_boxF_eq_toFinset, boxSV_card_boxF]; push_cast; ring


theorem bfe_amenability (hd : 1 ≤ d) :
    Tendsto (fun R => (boxSV_boundaryCard d (R + 1) : ℝ) / ((boxFinsetBK d R).card : ℝ))
      atTop (𝓝 0) := by
  
  have hg0 : Tendsto (fun R : ℕ => (2 * (d : ℝ)) / ((R : ℝ) + 1)) atTop (𝓝 0) := by
    apply tendsto_const_nhds.div_atTop
    exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hg : Tendsto (fun R : ℕ => (2 * (d : ℝ)) / ((R : ℝ) + 1) * (3 : ℝ) ^ d) atTop (𝓝 0) := by
    simpa using hg0.mul_const ((3 : ℝ) ^ d)
  apply squeeze_zero' (Eventually.of_forall (fun R => by positivity)) ?_ hg
  refine Eventually.of_forall (fun R => ?_)
  have hVpos : (0 : ℝ) < ((boxFinsetBK d R).card : ℝ) := by exact_mod_cast bkc_boxFinsetBK_card_pos d R
  have hV1pos : (0 : ℝ) < ((boxFinsetBK d (R + 1)).card : ℝ) := by
    exact_mod_cast bkc_boxFinsetBK_card_pos d (R + 1)
  
  have hfactor :
      (boxSV_boundaryCard d (R + 1) : ℝ) / ((boxFinsetBK d R).card : ℝ)
        = ((boxSV_boundaryCard d (R + 1) : ℝ) / ((boxFinsetBK d (R + 1)).card : ℝ))
          * (((boxFinsetBK d (R + 1)).card : ℝ) / ((boxFinsetBK d R).card : ℝ)) := by
    field_simp
  
  have key1 : (boxSV_boundaryCard d (R + 1) : ℝ) / ((boxFinsetBK d (R + 1)).card : ℝ)
      ≤ 2 * (d : ℝ) / ((R : ℝ) + 1) := by
    have h := bkc_boundary_vol_ratio_le d (R + 1) hd (by omega)
    have hcast : ((R + 1 : ℕ) : ℝ) = (R : ℝ) + 1 := by push_cast; ring
    rw [hcast] at h
    exact h
  
  have key2 : ((boxFinsetBK d (R + 1)).card : ℝ) / ((boxFinsetBK d R).card : ℝ) ≤ (3 : ℝ) ^ d := by
    rw [bfe_boxCard (R + 1), bfe_boxCard R, div_le_iff₀ (by positivity)]
    push_cast
    rw [← mul_pow]
    gcongr
    nlinarith [show (0 : ℝ) ≤ (R : ℝ) by positivity]
  
  have hnn1 : (0 : ℝ) ≤ ((boxFinsetBK d (R + 1)).card : ℝ) / ((boxFinsetBK d R).card : ℝ) :=
    le_of_lt (div_pos hV1pos hVpos)
  have hnn2 : (0 : ℝ) ≤ 2 * (d : ℝ) / ((R : ℝ) + 1) := by positivity
  rw [hfactor]
  exact mul_le_mul key1 key2 hnn1 hnn2


theorem bfe_dichotomy (hd : 1 ≤ d) (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) :
    μ {ω | bc61_IsCoarseTrifurcation ω 0 0} = 0 :=
  bpe_coarseTrif_prob_eq_zero_of_expBound μ 0 (fun R => boxSV_boundaryCard d (R + 1))
    (fun R => bfe_exp_eq μ hinv R) (fun R => bfe_expBound μ R)
    (fun R => bkc_boxFinsetBK_card_pos d R) (bfe_amenability hd)


theorem bfe_top_null (hd : 1 ≤ d) (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hexist : bc61_CoarseTrifExistence μ 0) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bpe_top_null_of_expCount μ 0 (fun R => boxSV_boundaryCard d (R + 1))
    (fun R => bfe_exp_eq μ hinv R) (fun R => bfe_expBound μ R)
    (fun R => bkc_boxFinsetBK_card_pos d R) (bfe_amenability hd) hexist


end StatMech.Walls

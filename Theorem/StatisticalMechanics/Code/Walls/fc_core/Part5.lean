/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.EdgeConfigZ.Part15
import Theorem.StatisticalMechanics.Code.Walls.fc_weightle
import Theorem.StatisticalMechanics.Code.Walls.fc_allclosed
import Theorem.StatisticalMechanics.Code.Walls.fc_bulkfraction
import Def.StatisticalMechanics.Code.Walls.fc_core.Part4
open scoped BigOperators
open SimpleGraph Filter Topology Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000


namespace StatMech

namespace Walls

open StatMech.FK StatMech.Lattice


variable {d : ℕ}


theorem fc_C_nonneg {q : ℝ} (hq : 1 ≤ q) : 0 ≤ fc_C q := by
  unfold fc_C
  have h1 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h2 : (0:ℝ) ≤ Real.log q := Real.log_nonneg hq
  linarith


theorem fc_edgeFE_le_const (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) {q : ℝ} (hq : 1 ≤ q) (s : ℝ)
    (hE : 0 < (boxGraph d n).edgeFinset.card) :
    fc_edgeFreeEnergy d q s n ≤ fc_C q + Real.log (1 + Real.exp s) := by
  unfold fc_edgeFreeEnergy fc_u
  set E := (boxGraph d n).edgeFinset.card with hEdef
  set V := Fintype.card (boxVerts d n) with hVdef
  set p := fsc_logistic s
  have hp0 : (0:ℝ) < p := fsc_logistic_pos s
  have hp1 : p < 1 := fsc_logistic_lt_one s
  have hEr : (0:ℝ) < (E:ℝ) := by exact_mod_cast hE
  have hZpos : 0 < ecz_fkZEdge (boxGraph d n) p q := ecz_fkZEdge_pos _ hp0 hp1 (by linarith)
  have hub : ecz_fkZEdge (boxGraph d n) p q ≤ (2:ℝ)^E * q^V :=
    fc_fkZEdge_le_qpow _ hp0.le hp1.le hq
  have hlogq : (0:ℝ) ≤ Real.log q := Real.log_nonneg hq
  have hlog2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hqpow : (0:ℝ) < q^V := by positivity
  have hlog : Real.log (ecz_fkZEdge (boxGraph d n) p q) ≤ (E:ℝ) * Real.log 2 + (V:ℝ) * Real.log q := by
    calc Real.log (ecz_fkZEdge (boxGraph d n) p q)
        ≤ Real.log ((2:ℝ)^E * q^V) := Real.log_le_log hZpos hub
      _ = (E:ℝ) * Real.log 2 + (V:ℝ) * Real.log q := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  have hVle : (V:ℝ) ≤ 2 * E := by exact_mod_cast ecz_boxVerts_le_edges d n hd hn
  
  have hkey : -(-Real.log (ecz_fkZEdge (boxGraph d n) p q) / (E:ℝ)) ≤ fc_C q := by
    rw [neg_div, neg_neg, div_le_iff₀ hEr]
    have hstep : (V:ℝ) * Real.log q ≤ (2 * E) * Real.log q :=
      mul_le_mul_of_nonneg_right hVle hlogq
    calc Real.log (ecz_fkZEdge (boxGraph d n) p q)
        ≤ (E:ℝ) * Real.log 2 + (V:ℝ) * Real.log q := hlog
      _ ≤ (E:ℝ) * Real.log 2 + (2 * E) * Real.log q := by linarith
      _ = fc_C q * E := by unfold fc_C; ring
  linarith


theorem fc_box_neglog_doubling (d K : ℕ) {q : ℝ} (hq : 1 ≤ q) (t : ℝ) :
    fc_u d q t (2 * K + 1) ≤ (2 : ℝ) ^ d * fc_u d q t K
      + ((2 * d * (qp_Jset d K).card + (2 ^ d + 1) * (2 * d * (qp_Jset d K).card) : ℕ) : ℝ)
          * (-Real.log (1 - fsc_logistic t)) := by
  set p := fsc_logistic t with hp
  have hp0 : (0 : ℝ) < p := fsc_logistic_pos t
  have hp1 : p < 1 := fsc_logistic_lt_one t
  have hq0 : (0:ℝ) < q := by linarith
  set c := -Real.log (1 - p) with hc
  have hc0 : 0 ≤ c := by rw [hc, neg_nonneg]; exact Real.log_nonpos (by linarith) (by linarith)
  obtain ⟨I, hIle, hIbd⟩ :=
    ecz_peel_le (boxGraph d (2 * K + 1)) (qp_boxTag d K) p q hp0 hp1 hq0 Finset.univ
  have hrest : ecz_uu (qp_restG (boxGraph d (2 * K + 1)) (qp_boxTag d K) Finset.univ) p q
      = fc_u d q t (2 * K + 1) := by
    rw [ecz_uu, fc_u, ecz_fkZEdge_iso (qp_restGUnivIso d K) p q]
  have hblksum : (∑ τ ∈ (Finset.univ : Finset (Option (Fin d → Bool))),
        ecz_uu (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) τ) p q)
      = ecz_uu (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) none) p q
        + (2 : ℝ) ^ d * fc_u d q t K := by
    rw [show (∑ τ ∈ (Finset.univ : Finset (Option (Fin d → Bool))),
            ecz_uu (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) τ) p q)
          = ∑ τ : Option (Fin d → Bool),
              ecz_uu (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) τ) p q from rfl,
      Fintype.sum_option]
    congr 1
    have heach : ∀ s : Fin d → Bool,
        ecz_uu (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) (some s)) p q = fc_u d q t K :=
      fun s => by rw [ecz_uu, ecz_block_fkZEdge]; rfl
    rw [Finset.sum_congr rfl (fun s _ => heach s), Finset.sum_const, Finset.card_univ,
      show Fintype.card (Fin d → Bool) = 2 ^ d from by simp [Fintype.card_fun, Fintype.card_bool],
      nsmul_eq_mul]
    push_cast; ring
  have hnone : ecz_uu (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) none) p q
      ≤ ((2 * d * (qp_Jset d K).card : ℕ) : ℝ) * c := by
    rw [ecz_uu]
    calc -Real.log (ecz_fkZEdge (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) none) p q)
        ≤ ((qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) none).edgeFinset.card : ℝ) * c :=
          ecz_neglogZEdge_le_edges _ hp0 hp1 hq
      _ ≤ ((2 * d * (qp_Jset d K).card : ℕ) : ℝ) * c := by
          apply mul_le_mul_of_nonneg_right _ hc0
          exact_mod_cast qp_blkNone_edge_le d K
  have hIbound : (I : ℝ) ≤ ((2 ^ d + 1) * (2 * d * (qp_Jset d K).card) : ℕ) := by
    have h2 : (∑ τ ∈ (Finset.univ : Finset (Option (Fin d → Bool))),
          (qp_straddleEdges (boxGraph d (2 * K + 1)) (fun u => qp_boxTag d K u = τ)).card)
        ≤ ∑ _τ ∈ (Finset.univ : Finset (Option (Fin d → Bool))), 2 * d * (qp_Jset d K).card :=
      Finset.sum_le_sum (fun τ _ => qp_straddle_card_le_all d K τ)
    have h3 : (∑ _τ ∈ (Finset.univ : Finset (Option (Fin d → Bool))), 2 * d * (qp_Jset d K).card)
        = (2 ^ d + 1) * (2 * d * (qp_Jset d K).card) := by
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      congr 1
      rw [show Fintype.card (Option (Fin d → Bool)) = Fintype.card (Fin d → Bool) + 1 from
          Fintype.card_option,
        show Fintype.card (Fin d → Bool) = 2 ^ d from by simp [Fintype.card_fun, Fintype.card_bool]]
    calc (I : ℝ) ≤ ((∑ τ ∈ (Finset.univ : Finset (Option (Fin d → Bool))),
            (qp_straddleEdges (boxGraph d (2 * K + 1)) (fun u => qp_boxTag d K u = τ)).card : ℕ) : ℝ) := by
          exact_mod_cast hIbd
      _ ≤ (((2 ^ d + 1) * (2 * d * (qp_Jset d K).card) : ℕ) : ℝ) := by
          exact_mod_cast le_trans h2 (le_of_eq h3)
  rw [hrest, hblksum] at hIle
  push_cast at hIle hnone hIbound ⊢
  nlinarith [hIle, hnone, hIbound, hc0, mul_le_mul_of_nonneg_right hIbound hc0]


end Walls
end StatMech

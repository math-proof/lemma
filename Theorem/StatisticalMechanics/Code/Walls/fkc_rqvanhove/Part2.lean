/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqvanhove.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.fkc_rqbdd.Part2
import Theorem.StatisticalMechanics.Code.Walls.fkc_rqbulkfraction
import Def.StatisticalMechanics.Code.Walls.fkc_rqvanhove.Part2
open scoped BigOperators
open SimpleGraph Filter Topology Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 2000000


namespace StatMech.Walls

open StatMech StatMech.FK StatMech.Lattice


theorem fkc_additiveDoublingBound (d : ℕ) (hd : 1 ≤ d) (s q : ℝ) (hq : 1 ≤ q) :
    fkc_AdditiveDoublingBound d s q := by
  set c := -Real.log (1 - fsc_logistic s) with hc
  have hp0 : (0 : ℝ) < fsc_logistic s := fsc_logistic_pos s
  have hp1 : fsc_logistic s < 1 := fsc_logistic_lt_one s
  have hc0 : 0 ≤ c := by
    rw [hc, neg_nonneg]
    exact Real.log_nonpos (by linarith) (by linarith)
  set N : ℕ → ℝ := fun j => ((2 * d * (qp_Jset d (agl_K j)).card
    + (2 ^ d + 1) * (2 * d * (qp_Jset d (agl_K j)).card) : ℕ) : ℝ) with hN
  set G : ℕ → ℝ := fun j => agl_E d (agl_K (j + 1)) - (2 : ℝ) ^ d * agl_E d (agl_K j) with hG
  have hGnn : ∀ j, 0 ≤ G j := by
    intro j
    rw [hG]; simp only
    have h := qp_edge_le d (agl_K j) hd
    rw [show agl_E d (agl_K (j + 1)) = agl_E d (2 * agl_K j + 1) by rw [agl_K_succ]]
    rw [agl_E, agl_E]
    linarith
  set I : ℕ → ℝ := fun j => N j + G j with hI
  have hInn : ∀ j, 0 ≤ I j := by
    intro j; rw [hI]; exact add_nonneg (Nat.cast_nonneg _) (hGnn j)
  refine ⟨I, hInn, ?_, ?_, ?_⟩
  · apply qp_summable_ratio d hd I _ hInn
    intro j
    have hNb : N j ≤ ((2 ^ d + 2) * (2 * d * d) : ℝ) * (4 * (agl_K j : ℝ) + 3) ^ (d - 1) := by
      simp only [hN]
      have hJ := qp_Jset_card_le d (agl_K j) hd
      rw [show (2 * d * (qp_Jset d (agl_K j)).card
          + (2 ^ d + 1) * (2 * d * (qp_Jset d (agl_K j)).card))
          = (2 ^ d + 2) * (2 * d * (qp_Jset d (agl_K j)).card) by ring]
      push_cast
      have hJR : ((qp_Jset d (agl_K j)).card : ℝ)
          ≤ (d : ℝ) * (4 * (agl_K j : ℝ) + 3) ^ (d - 1) := by
        calc ((qp_Jset d (agl_K j)).card : ℝ)
            ≤ ((d * (2 * (2 * agl_K j + 1) + 1) ^ (d - 1) : ℕ) : ℝ) := by exact_mod_cast hJ
          _ = (d : ℝ) * (4 * (agl_K j : ℝ) + 3) ^ (d - 1) := by push_cast; ring
      calc ((2 : ℝ) ^ d + 2) * (2 * d * ((qp_Jset d (agl_K j)).card : ℝ))
          ≤ ((2 : ℝ) ^ d + 2) * (2 * d * ((d : ℝ) * (4 * (agl_K j : ℝ) + 3) ^ (d - 1))) := by
            gcongr
        _ = ((2 : ℝ) ^ d + 2) * (2 * d * d) * (4 * (agl_K j : ℝ) + 3) ^ (d - 1) := by ring
    have hGb : G j ≤ ((d : ℝ) * (d + 2)) * (4 * (agl_K j : ℝ) + 3) ^ (d - 1) := by
      rw [hG]; simp only
      rw [show agl_E d (agl_K (j + 1)) = agl_E d (2 * agl_K j + 1) by rw [agl_K_succ]]
      have h := qp_edge_gap_le d (agl_K j) hd
      rw [agl_E, agl_E]
      linarith
    rw [hI]
    linarith
  · intro j
    have hdbl := fkc_box_neglog_doubling d (agl_K j) s q hq
    rw [show fkc_u d s q (agl_K (j + 1)) = fkc_u d s q (2 * agl_K j + 1) by rw [agl_K_succ]]
    have hge : N j * c ≤ I j * c := by
      apply mul_le_mul_of_nonneg_right _ hc0
      rw [hI]
      exact le_add_of_nonneg_right (hGnn j)
    calc fkc_u d s q (2 * agl_K j + 1)
        ≤ (2 : ℝ) ^ d * fkc_u d s q (agl_K j) + N j * c := hdbl
      _ ≤ (2 : ℝ) ^ d * fkc_u d s q (agl_K j) + I j * c := by linarith
  · intro j
    rw [abs_of_nonpos]
    · rw [hI, hG]
      have hN0 : 0 ≤ N j := Nat.cast_nonneg _
      linarith
    · rw [hG] at hGnn
      linarith [hGnn j]


theorem fkc_dyadic_f_tendsto (d : ℕ) (hd : 1 ≤ d) (s q : ℝ) (hq : 1 ≤ q) :
    ∃ L : ℝ, Tendsto (fun j => fkc_f d s q (agl_K j)) atTop (nhds L) := by
  classical
  obtain ⟨I, hInn, hIsum, hudbl, hEdge⟩ := fkc_additiveDoublingBound d hd s q hq
  set c : ℝ := -Real.log (1 - fsc_logistic s) with hc
  have hp0 : (0 : ℝ) < fsc_logistic s := fsc_logistic_pos s
  have hp1 : fsc_logistic s < 1 := fsc_logistic_lt_one s
  have hc0 : 0 ≤ c := by
    rw [hc, neg_nonneg]
    exact Real.log_nonpos (by linarith) (by linarith)
  have hEpos : ∀ j, 0 < agl_E d (agl_K j) := fun j => by
    unfold agl_E
    exact_mod_cast ecz_box_edge_pos d hd (agl_K_pos j)
  set M : ℝ := Real.log 2 + 2 * Real.log q + c with hM
  have hMpc0 : 0 ≤ M + c := by
    rw [hM]
    have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlogq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq
    linarith
  have hIE0 : ∀ j, 0 ≤ I j / agl_E d (agl_K (j + 1)) := fun j =>
    div_nonneg (hInn j) (hEpos (j + 1)).le
  set δ : ℕ → ℝ := fun j => (M + c) * (I j / agl_E d (agl_K (j + 1))) with hδ
  have hmono : ∀ j, fkc_edgeFreeEnergy d s q (agl_K j) - δ j
      ≤ fkc_edgeFreeEnergy d s q (agl_K (j + 1)) := by
    intro j
    rw [fkc_edgeFreeEnergy_eq, fkc_edgeFreeEnergy_eq]
    have hstep := bxt_perVolume_doubling_step
      (a := fkc_u d s q (agl_K j)) (A := fkc_u d s q (agl_K (j + 1)))
      (e := agl_E d (agl_K j)) (E := agl_E d (agl_K (j + 1)))
      (K := (2 : ℝ) ^ d) (c := c) (i := I j)
      (hEpos j) (hEpos (j + 1)) hc0 (hInn j) (hudbl j) (hEdge j)
    have hupper : -(fkc_u d s q (agl_K j) / agl_E d (agl_K j))
        ≤ Real.log 2 + 2 * Real.log q := by
      have h := fkc_rq_bdd d (agl_K j) hd (agl_K_pos j) s q hq
      have h' : -(fkc_u d s q (agl_K j) / agl_E d (agl_K j))
          + Real.log (1 + Real.exp s)
          ≤ (Real.log 2 + 2 * Real.log q) + Real.log (1 + Real.exp s) := by
        simpa [fkc_edgeFreeEnergy_eq, fkc_f, agl_E] using h
      linarith
    have hlower : fkc_u d s q (agl_K j) / agl_E d (agl_K j) ≤ c := by
      have hge := ecz_neglogZEdge_le_edges (boxGraph d (agl_K j))
        (fsc_logistic_pos s) (fsc_logistic_lt_one s) hq
      rw [div_le_iff₀ (hEpos j)]
      have : fkc_u d s q (agl_K j) ≤ agl_E d (agl_K j) * c := by
        simpa [fkc_u, agl_E, hc] using hge
      linarith
    have huEbd : |fkc_u d s q (agl_K j)| / agl_E d (agl_K j) ≤ M := by
      rw [show |fkc_u d s q (agl_K j)| / agl_E d (agl_K j)
          = |fkc_u d s q (agl_K j) / agl_E d (agl_K j)| by
            rw [abs_div, abs_of_pos (hEpos j)], abs_le]
      have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hlogq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq
      constructor <;> rw [hM] <;> linarith
    have hdefle : (|fkc_u d s q (agl_K j)| / agl_E d (agl_K j) + c)
        * (I j / agl_E d (agl_K (j + 1))) ≤ δ j := by
      apply mul_le_mul_of_nonneg_right _ (hIE0 j)
      linarith
    have hgoal : -(fkc_u d s q (agl_K j) / agl_E d (agl_K j)) - δ j
        ≤ -(fkc_u d s q (agl_K (j + 1)) / agl_E d (agl_K (j + 1))) := by
      linarith
    change -(fkc_u d s q (agl_K j) / agl_E d (agl_K j))
        + Real.log (1 + Real.exp s) - δ j
      ≤ -(fkc_u d s q (agl_K (j + 1)) / agl_E d (agl_K (j + 1)))
        + Real.log (1 + Real.exp s)
    linarith
  have hbdd : BddAbove (Set.range fun j => fkc_edgeFreeEnergy d s q (agl_K j)) := by
    refine ⟨(Real.log 2 + 2 * Real.log q) + Real.log (1 + Real.exp s), ?_⟩
    rintro x ⟨j, rfl⟩
    exact fkc_rq_bdd d (agl_K j) hd (agl_K_pos j) s q hq
  obtain ⟨L', hL'⟩ := agl_subseq_almost_mono_converges
    (fun n => fkc_edgeFreeEnergy d s q n) agl_K δ
    (fun j => mul_nonneg hMpc0 (hIE0 j)) (hIsum.mul_left (M + c)) hmono hbdd
  refine ⟨Real.log (1 + Real.exp s) - L', ?_⟩
  have heq : ∀ j, fkc_f d s q (agl_K j)
      = Real.log (1 + Real.exp s) - fkc_edgeFreeEnergy d s q (agl_K j) := by
    intro j; rw [fkc_edgeFreeEnergy_eq]; ring
  rw [show (fun j => fkc_f d s q (agl_K j))
      = fun j => Real.log (1 + Real.exp s) - fkc_edgeFreeEnergy d s q (agl_K j) from funext heq]
  simpa using hL'.const_sub (Real.log (1 + Real.exp s))


end StatMech.Walls

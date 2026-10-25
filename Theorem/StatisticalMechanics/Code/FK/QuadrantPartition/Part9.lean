/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.AdditiveGluing.Part9
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Def.StatisticalMechanics.Code.FK.QuadrantPartition.Part11
open scoped BigOperators
open SimpleGraph Filter Topology Set MeasureTheory

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

namespace FK

open StatMech.Lattice


variable {U : Type*} [Fintype U] [DecidableEq U] (K₀ : SimpleGraph U) [DecidableRel K₀.Adj]


section BoxGeom

theorem qp_restG_univ_fkZ (d K : ℕ) (p q : ℝ) :
    fkZ (qp_restG (boxGraph d (2 * K + 1)) (qp_boxTag d K) Finset.univ) p q
      = fkZ (boxGraph d (2 * K + 1)) p q :=
  fsm_fkZ_iso _ _ (qp_restGUnivIso d K) p q


theorem qp_box_neglog_doubling (d K : ℕ) (t : ℝ) :
    agl_u d t (2 * K + 1) ≤ (2 : ℝ) ^ d * agl_u d t K
      + ((2 * d * (qp_Jset d K).card + (2 ^ d + 1) * (2 * d * (qp_Jset d K).card) : ℕ) : ℝ)
          * (-Real.log (1 - fsc_logistic t)) := by
  set p := fsc_logistic t with hp
  have hp0 : (0 : ℝ) < p := fsc_logistic_pos t
  have hp1 : p < 1 := fsc_logistic_lt_one t
  set c := -Real.log (1 - p) with hc
  have hc0 : 0 ≤ c := by rw [hc, neg_nonneg]; exact Real.log_nonpos (by linarith) (by linarith)
  obtain ⟨I, hIle, hIbd⟩ :=
    qp_peel_le (boxGraph d (2 * K + 1)) (qp_boxTag d K) p 2 hp0 hp1 (by norm_num) Finset.univ
  have hrest : qp_uu (qp_restG (boxGraph d (2 * K + 1)) (qp_boxTag d K) Finset.univ) p 2
      = agl_u d t (2 * K + 1) := by rw [qp_uu, qp_restG_univ_fkZ]; rfl
  have hblksum : (∑ τ ∈ (Finset.univ : Finset (Option (Fin d → Bool))),
        qp_uu (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) τ) p 2)
      = qp_uu (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) none) p 2 + (2 : ℝ) ^ d * agl_u d t K := by
    rw [show (∑ τ ∈ (Finset.univ : Finset (Option (Fin d → Bool))),
            qp_uu (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) τ) p 2)
          = ∑ τ : Option (Fin d → Bool),
              qp_uu (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) τ) p 2 from rfl,
      Fintype.sum_option]
    congr 1
    have heach : ∀ s : Fin d → Bool,
        qp_uu (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) (some s)) p 2 = agl_u d t K :=
      fun s => by rw [qp_uu, qp_block_fkZ]; rfl
    rw [Finset.sum_congr rfl (fun s _ => heach s), Finset.sum_const, Finset.card_univ,
      show Fintype.card (Fin d → Bool) = 2 ^ d from by simp [Fintype.card_fun, Fintype.card_bool],
      nsmul_eq_mul]
    push_cast; ring
  have hnone : qp_uu (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) none) p 2
      ≤ ((2 * d * (qp_Jset d K).card : ℕ) : ℝ) * c := by
    rw [qp_uu]
    calc -Real.log (fkZ (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) none) p 2)
        ≤ ((qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) none).edgeFinset.card : ℝ) * c :=
          qp_neglogZ_le_edges _ hp0 hp1 (by norm_num)
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


theorem qp_edge_le (d K : ℕ) (hd : 1 ≤ d) :
    (2 : ℝ) ^ d * ((boxGraph d K).edgeFinset.card) ≤ ((boxGraph d (2 * K + 1)).edgeFinset.card) := by
  rw [EdgeCount.boxGraph_edgeCard d K hd, EdgeCount.boxGraph_edgeCard d (2 * K + 1) hd]
  push_cast
  have key : (2 : ℝ) ^ d * (2 * K * (2 * K + 1) ^ (d - 1))
      ≤ (2 * (2 * K + 1)) * (2 * (2 * K + 1) + 1) ^ (d - 1) := by
    have h2d : (2 : ℝ) ^ d = 2 * 2 ^ (d - 1) := by rw [← pow_succ']; congr 1; omega
    rw [h2d, show (2 : ℝ) * 2 ^ (d - 1) * (2 * K * (2 * K + 1) ^ (d - 1))
          = (4 * K) * (2 * (2 * K + 1)) ^ (d - 1) by rw [mul_pow]; ring,
      show (2 : ℝ) * (2 * K + 1) = 4 * K + 2 by ring]
    apply mul_le_mul
    · linarith
    · apply pow_le_pow_left₀ (by positivity); linarith
    · positivity
    · positivity
  nlinarith [key, Nat.cast_nonneg (α := ℝ) d]


theorem qp_edge_gap_le (d K : ℕ) (hd : 1 ≤ d) :
    (((boxGraph d (2 * K + 1)).edgeFinset.card : ℝ)) - (2 : ℝ) ^ d * ((boxGraph d K).edgeFinset.card)
      ≤ (d : ℝ) * (d + 2) * (4 * K + 3) ^ (d - 1) := by
  rw [EdgeCount.boxGraph_edgeCard d K hd, EdgeCount.boxGraph_edgeCard d (2 * K + 1) hd]
  push_cast
  rw [show (2 * (2 * (K : ℝ) + 1) + 1) = 4 * K + 3 by ring,
    show (2 * (2 * (K : ℝ) + 1)) = 4 * K + 2 by ring]
  have h2d : (2 : ℝ) ^ d = 2 * 2 ^ (d - 1) := by rw [← pow_succ']; congr 1; omega
  rw [h2d,
    show (2 : ℝ) * 2 ^ (d - 1) * ((d : ℝ) * (2 * K * (2 * K + 1) ^ (d - 1)))
        = (d : ℝ) * ((4 * K) * (2 * (2 * K + 1)) ^ (d - 1)) by rw [mul_pow]; ring,
    show (2 : ℝ) * (2 * K + 1) = 4 * K + 2 by ring,
    ← mul_sub,
    show (d : ℝ) * (d + 2) * (4 * K + 3) ^ (d - 1) = (d : ℝ) * ((d + 2) * (4 * K + 3) ^ (d - 1)) by ring]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [show (4 * (K : ℝ) + 2) * (4 * K + 3) ^ (d - 1) - (4 * K) * (4 * K + 2) ^ (d - 1)
        = (4 * K + 2) * ((4 * K + 3) ^ (d - 1) - (4 * K + 2) ^ (d - 1)) + 2 * (4 * K + 2) ^ (d - 1)
      by ring]
  have hpow := boxSV_pow_sub_pow_le (4 * (K : ℝ) + 3) (4 * K + 2) (by positivity) (by linarith) (d - 1)
  rw [show (4 * (K : ℝ) + 3) - (4 * K + 2) = 1 by ring, one_mul] at hpow
  have h1 : (4 * (K : ℝ) + 2) * ((4 * K + 3) ^ (d - 1) - (4 * K + 2) ^ (d - 1))
      ≤ (4 * K + 2) * (((d - 1 : ℕ) : ℝ) * (4 * K + 3) ^ (d - 1 - 1)) :=
    mul_le_mul_of_nonneg_left hpow (by positivity)
  have h2 : (4 * (K : ℝ) + 2) * (((d - 1 : ℕ) : ℝ) * (4 * K + 3) ^ (d - 1 - 1))
      ≤ ((d : ℝ) - 1) * (4 * K + 3) ^ (d - 1) := by
    rcases Nat.lt_or_ge d 2 with h | h
    · have hd1 : d = 1 := by omega
      subst hd1; simp
    · have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
      rw [hcast, show (4 * (K : ℝ) + 3) ^ (d - 1) = (4 * K + 3) * (4 * K + 3) ^ (d - 1 - 1) from by
            rw [← pow_succ']; congr 1; omega,
        show (4 * (K : ℝ) + 2) * (((d : ℝ) - 1) * (4 * K + 3) ^ (d - 1 - 1))
            = ((d : ℝ) - 1) * ((4 * K + 2) * (4 * K + 3) ^ (d - 1 - 1)) by ring]
      have hdpos : (0 : ℝ) ≤ (d : ℝ) - 1 := by
        have : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
        linarith
      apply mul_le_mul_of_nonneg_left _ hdpos
      apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have h3 : (2 : ℝ) * (4 * K + 2) ^ (d - 1) ≤ 2 * (4 * K + 3) ^ (d - 1) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply pow_le_pow_left₀ (by positivity); linarith
  calc (4 * (K : ℝ) + 2) * ((4 * K + 3) ^ (d - 1) - (4 * K + 2) ^ (d - 1)) + 2 * (4 * K + 2) ^ (d - 1)
      ≤ (d - 1) * (4 * K + 3) ^ (d - 1) + 2 * (4 * K + 3) ^ (d - 1) := by linarith [le_trans h1 h2, h3]
    _ = (d + 1) * (4 * K + 3) ^ (d - 1) := by ring
    _ ≤ (d + 2) * (4 * K + 3) ^ (d - 1) := by
        apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end BoxGeom


theorem qp_edge_lower (d n : ℕ) (hd : 1 ≤ d) :
    (n : ℝ) * (2 * (n : ℝ) + 1) ^ (d - 1) ≤ ((boxGraph d n).edgeFinset.card : ℝ) := by
  have h1 := boxSV_edge_card_lower (d := d) (n := n) hd
  rw [fup_edge_card_eq d n] at h1
  have hnat : n * (2 * n + 1) ^ (d - 1) ≤ (boxGraph d n).edgeFinset.card := by
    have h2 : 2 * (n * (2 * n + 1) ^ (d - 1)) ≤ 2 * (boxGraph d n).edgeFinset.card := by
      rw [show 2 * (n * (2 * n + 1) ^ (d - 1)) = (2 * n) * (2 * n + 1) ^ (d - 1) by ring]; exact h1
    omega
  calc (n : ℝ) * (2 * (n : ℝ) + 1) ^ (d - 1) = ((n * (2 * n + 1) ^ (d - 1) : ℕ) : ℝ) := by
        push_cast; ring
    _ ≤ ((boxGraph d n).edgeFinset.card : ℝ) := by exact_mod_cast hnat


theorem qp_summable_ratio (d : ℕ) (hd : 1 ≤ d) (I : ℕ → ℝ)
    (hIbd : ∀ j, I j ≤ ((2 ^ d + 2) * (2 * d * d) + d * (d + 2) : ℝ) * (4 * (agl_K j : ℝ) + 3) ^ (d - 1))
    (hI0 : ∀ j, 0 ≤ I j) :
    Summable (fun j => I j / agl_E d (agl_K (j + 1))) := by
  set Ctot : ℝ := ((2 ^ d + 2) * (2 * d * d) + d * (d + 2) : ℝ) with hCtot
  have hCtot0 : 0 ≤ Ctot := by rw [hCtot]; positivity
  refine Summable.of_nonneg_of_le (f := fun j => Ctot * (1 / 2 : ℝ) ^ j)
    (fun j => div_nonneg (hI0 j) (by rw [agl_E]; positivity)) ?_
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left Ctot)
  intro j
  have hKsucc : agl_K (j + 1) = 2 * agl_K j + 1 := agl_K_succ j
  have hKR : (agl_K (j + 1) : ℝ) = 2 * (agl_K j : ℝ) + 1 := by rw [hKsucc]; push_cast; ring
  have hbase : 2 * (agl_K (j + 1) : ℝ) + 1 = 4 * (agl_K j : ℝ) + 3 := by rw [hKR]; ring
  have hElow : (agl_K (j + 1) : ℝ) * (4 * (agl_K j : ℝ) + 3) ^ (d - 1) ≤ agl_E d (agl_K (j + 1)) := by
    have h := qp_edge_lower d (agl_K (j + 1)) hd
    rw [agl_E, ← hbase]; exact h
  have hKj1pos : (0 : ℝ) < (agl_K (j + 1) : ℝ) := by exact_mod_cast agl_K_pos (j + 1)
  have hpowpos : (0 : ℝ) < (4 * (agl_K j : ℝ) + 3) ^ (d - 1) := by positivity
  calc I j / agl_E d (agl_K (j + 1))
      ≤ (Ctot * (4 * (agl_K j : ℝ) + 3) ^ (d - 1))
          / ((agl_K (j + 1) : ℝ) * (4 * (agl_K j : ℝ) + 3) ^ (d - 1)) :=
        div_le_div₀ (by positivity) (hIbd j) (by positivity) hElow
    _ = Ctot / (agl_K (j + 1) : ℝ) := by rw [mul_div_mul_right _ _ (ne_of_gt hpowpos)]
    _ ≤ Ctot * (1 / 2 : ℝ) ^ j := by
        have hKge : (2 : ℝ) ^ j ≤ (agl_K (j + 1) : ℝ) := by
          have hnat : (2 : ℕ) ^ j ≤ agl_K (j + 1) := by
            unfold agl_K
            have h1 : 2 ^ j ≤ 2 ^ (j + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
            have h2 : 1 ≤ 2 ^ (j + 1 + 1) := Nat.one_le_two_pow
            omega
          exact_mod_cast hnat
        have h2jpos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
        rw [show (1 / 2 : ℝ) ^ j = ((2 : ℝ) ^ j)⁻¹ from by rw [one_div, inv_pow],
          div_eq_mul_inv]
        apply mul_le_mul_of_nonneg_left _ hCtot0
        rw [inv_le_inv₀ hKj1pos h2jpos]; exact hKge


theorem qp_additiveDoublingBound (d : ℕ) (hd : 1 ≤ d) (t : ℝ) : agl_AdditiveDoublingBound d t := by
  set c := -Real.log (1 - fsc_logistic t) with hc
  have hp0 : (0 : ℝ) < fsc_logistic t := fsc_logistic_pos t
  have hp1 : fsc_logistic t < 1 := fsc_logistic_lt_one t
  have hc0 : 0 ≤ c := by rw [hc, neg_nonneg]; exact Real.log_nonpos (by linarith) (by linarith)
  set N : ℕ → ℝ := fun j => ((2 * d * (qp_Jset d (agl_K j)).card
    + (2 ^ d + 1) * (2 * d * (qp_Jset d (agl_K j)).card) : ℕ) : ℝ) with hN
  set G : ℕ → ℝ := fun j => agl_E d (agl_K (j + 1)) - (2 : ℝ) ^ d * agl_E d (agl_K j) with hG
  have hKsucc : ∀ j, agl_K (j + 1) = 2 * agl_K j + 1 := agl_K_succ
  have hGnn : ∀ j, 0 ≤ G j := by
    intro j; rw [hG]; simp only
    have h := qp_edge_le d (agl_K j) hd
    rw [show agl_E d (agl_K (j + 1)) = agl_E d (2 * agl_K j + 1) from by rw [agl_K_succ]]
    rw [agl_E, agl_E]; linarith [h]
  set I : ℕ → ℝ := fun j => N j + G j with hI
  have hInn : ∀ j, 0 ≤ I j := by
    intro j; rw [hI]; have : 0 ≤ N j := Nat.cast_nonneg _; linarith [hGnn j]
  refine ⟨I, hInn, ?_, ?_, ?_⟩
  · 
    apply qp_summable_ratio d hd I _ hInn
    intro j
    
    have hNb : N j ≤ ((2 ^ d + 2) * (2 * d * d) : ℝ) * (4 * (agl_K j : ℝ) + 3) ^ (d - 1) := by
      simp only [hN]
      have hJ : (qp_Jset d (agl_K j)).card ≤ d * (2 * (2 * agl_K j + 1) + 1) ^ (d - 1) :=
        qp_Jset_card_le d (agl_K j) hd
      rw [show (2 * d * (qp_Jset d (agl_K j)).card + (2 ^ d + 1) * (2 * d * (qp_Jset d (agl_K j)).card))
            = (2 ^ d + 2) * (2 * d * (qp_Jset d (agl_K j)).card) from by ring]
      push_cast
      have hbase : (2 * (2 * (agl_K j : ℝ) + 1) + 1) = 4 * (agl_K j : ℝ) + 3 := by ring
      have hJR : ((qp_Jset d (agl_K j)).card : ℝ)
          ≤ (d : ℝ) * (4 * (agl_K j : ℝ) + 3) ^ (d - 1) := by
        calc ((qp_Jset d (agl_K j)).card : ℝ)
            ≤ ((d * (2 * (2 * agl_K j + 1) + 1) ^ (d - 1) : ℕ) : ℝ) := by exact_mod_cast hJ
          _ = (d : ℝ) * (2 * (2 * (agl_K j : ℝ) + 1) + 1) ^ (d - 1) := by push_cast; ring
          _ = (d : ℝ) * (4 * (agl_K j : ℝ) + 3) ^ (d - 1) := by rw [hbase]
      calc ((2 : ℝ) ^ d + 2) * (2 * d * ((qp_Jset d (agl_K j)).card : ℝ))
          ≤ ((2 : ℝ) ^ d + 2) * (2 * d * ((d : ℝ) * (4 * (agl_K j : ℝ) + 3) ^ (d - 1))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply mul_le_mul_of_nonneg_left hJR (by positivity)
        _ = ((2 : ℝ) ^ d + 2) * (2 * d * d) * (4 * (agl_K j : ℝ) + 3) ^ (d - 1) := by ring
    have hGb : G j ≤ ((d : ℝ) * (d + 2)) * (4 * (agl_K j : ℝ) + 3) ^ (d - 1) := by
      rw [hG]; simp only
      rw [show agl_E d (agl_K (j + 1)) = agl_E d (2 * agl_K j + 1) from by rw [agl_K_succ]]
      have h := qp_edge_gap_le d (agl_K j) hd
      rw [agl_E, agl_E]; linarith [h]
    rw [hI]; linarith [hNb, hGb]
  · 
    intro j
    have hdbl := qp_box_neglog_doubling d (agl_K j) t
    rw [show agl_u d t (agl_K (j + 1)) = agl_u d t (2 * agl_K j + 1) from by rw [agl_K_succ]]
    have hge : N j * c ≤ I j * c := by
      rw [hI]; apply mul_le_mul_of_nonneg_right _ hc0; linarith [hGnn j]
    calc agl_u d t (2 * agl_K j + 1)
        ≤ (2 : ℝ) ^ d * agl_u d t (agl_K j) + N j * c := hdbl
      _ ≤ (2 : ℝ) ^ d * agl_u d t (agl_K j) + I j * c := by linarith
  · 
    intro j
    have hGval : G j = agl_E d (agl_K (j + 1)) - (2 : ℝ) ^ d * agl_E d (agl_K j) := rfl
    rw [abs_of_nonpos (by have := hGnn j; rw [hGval] at this; linarith)]
    rw [hI]; have hNn : 0 ≤ N j := Nat.cast_nonneg _
    have hGeq : -((2 : ℝ) ^ d * agl_E d (agl_K j) - agl_E d (agl_K (j + 1))) = G j := by
      rw [hGval]; ring
    rw [hGeq]; linarith


theorem qp_additiveBoxFeketeData (d : ℕ) (hd : 1 ≤ d) (t : ℝ)
    (hbdd : ∃ M : ℝ, ∀ j, |agl_u d t (agl_K j) / agl_E d (agl_K j)| ≤ M)
    (hosc : ∃ (bj : ℕ → ℕ) (osc : ℕ → ℝ), Tendsto bj atTop atTop ∧ Tendsto osc atTop (𝓝 0)
        ∧ (∀ n, |ivp2_tiltFreeEnergy (boxGraph d n) 2 t
            - ivp2_tiltFreeEnergy (boxGraph d (agl_K (bj n))) 2 t| ≤ osc (bj n))) :
    agl_AdditiveBoxFeketeData d t :=
  ⟨qp_additiveDoublingBound d hd t, hbdd, hosc⟩


theorem qp_fk_uniqueness (d : ℕ) (hd : 1 ≤ d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    (heb : eb ∈ (boxGraph d N).edgeFinset)
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    (hbdd : ∀ t, ∃ M : ℝ, ∀ j, |agl_u d t (agl_K j) / agl_E d (agl_K j)| ≤ M)
    (hosc : ∀ t, ∃ (bj : ℕ → ℕ) (osc : ℕ → ℝ), Tendsto bj atTop atTop ∧ Tendsto osc atTop (𝓝 0)
        ∧ (∀ n, |ivp2_tiltFreeEnergy (boxGraph d n) 2 t
            - ivp2_tiltFreeEnergy (boxGraph d (agl_K (bj n))) 2 t| ≤ osc (bj n))) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable :=
  agl_fk_uniqueness_of_additiveData d hd N eb heb hEbox
    (fun t => qp_additiveBoxFeketeData d hd t (hbdd t) (hosc t))

end FK
end StatMech

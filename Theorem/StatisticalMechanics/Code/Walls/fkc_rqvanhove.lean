/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqvanhove.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.fkc_rqbdd.Part2
import Theorem.StatisticalMechanics.Code.Walls.fkc_rqbulkfraction
import Def.StatisticalMechanics.Code.Walls.fkc_rqvanhove
open scoped BigOperators
open SimpleGraph Filter Topology Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 2000000


namespace StatMech.Walls

open StatMech StatMech.FK StatMech.Lattice


theorem fkc_edgeFreeEnergy_eq (d : ℕ) (s q : ℝ) (n : ℕ) :
    fkc_edgeFreeEnergy d s q n = -fkc_f d s q n + Real.log (1 + Real.exp s) := by
  unfold fkc_edgeFreeEnergy fkc_f fkc_u
  rw [neg_div, neg_neg]


@[simp] theorem fkc_u_q2 (d : ℕ) (s : ℝ) (n : ℕ) : fkc_u d s 2 n = ecz_u d s n := rfl


theorem fkc_box_neglog_doubling (d K : ℕ) (s q : ℝ) (hq : 1 ≤ q) :
    fkc_u d s q (2 * K + 1) ≤ (2 : ℝ) ^ d * fkc_u d s q K
      + ((2 * d * (qp_Jset d K).card + (2 ^ d + 1) * (2 * d * (qp_Jset d K).card) : ℕ) : ℝ)
          * (-Real.log (1 - fsc_logistic s)) := by
  set p := fsc_logistic s with hp
  have hp0 : (0 : ℝ) < p := fsc_logistic_pos s
  have hp1 : p < 1 := fsc_logistic_lt_one s
  set c := -Real.log (1 - p) with hc
  have hc0 : 0 ≤ c := by rw [hc, neg_nonneg]; exact Real.log_nonpos (by linarith) (by linarith)
  obtain ⟨I, hIle, hIbd⟩ :=
    ecz_peel_le (boxGraph d (2 * K + 1)) (qp_boxTag d K) p q hp0 hp1 (by linarith) Finset.univ
  have hrest : ecz_uu (qp_restG (boxGraph d (2 * K + 1)) (qp_boxTag d K) Finset.univ) p q
      = fkc_u d s q (2 * K + 1) := by
    rw [ecz_uu, fkc_u, ecz_fkZEdge_iso (qp_restGUnivIso d K) p q]
  have hblksum : (∑ τ ∈ (Finset.univ : Finset (Option (Fin d → Bool))),
        ecz_uu (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) τ) p q)
      = ecz_uu (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) none) p q
        + (2 : ℝ) ^ d * fkc_u d s q K := by
    rw [show (∑ τ ∈ (Finset.univ : Finset (Option (Fin d → Bool))),
            ecz_uu (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) τ) p q)
          = ∑ τ : Option (Fin d → Bool),
              ecz_uu (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) τ) p q from rfl,
      Fintype.sum_option]
    congr 1
    have heach : ∀ t : Fin d → Bool,
        ecz_uu (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) (some t)) p q
          = fkc_u d s q K := fun t => by
      rw [ecz_uu, fkc_u, ecz_block_fkZEdge]
    rw [Finset.sum_congr rfl (fun t _ => heach t), Finset.sum_const, Finset.card_univ,
      show Fintype.card (Fin d → Bool) = 2 ^ d from by simp [Fintype.card_bool],
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
    have h3 : (∑ _τ ∈ (Finset.univ : Finset (Option (Fin d → Bool))),
          2 * d * (qp_Jset d K).card)
        = (2 ^ d + 1) * (2 * d * (qp_Jset d K).card) := by
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      congr 1
      rw [Fintype.card_option,
        show Fintype.card (Fin d → Bool) = 2 ^ d from by simp [Fintype.card_bool]]
    calc (I : ℝ) ≤ ((∑ τ ∈ (Finset.univ : Finset (Option (Fin d → Bool))),
            (qp_straddleEdges (boxGraph d (2 * K + 1)) (fun u => qp_boxTag d K u = τ)).card : ℕ) : ℝ) := by
          exact_mod_cast hIbd
      _ ≤ (((2 ^ d + 1) * (2 * d * (qp_Jset d K).card) : ℕ) : ℝ) := by
          exact_mod_cast le_trans h2 (le_of_eq h3)
  rw [hrest, hblksum] at hIle
  push_cast at hIle hnone hIbound ⊢
  nlinarith [hIle, hnone, hIbound, hc0, mul_le_mul_of_nonneg_right hIbound hc0]


theorem fkc_box_vanHove_subadd (d m n : ℕ) (s q : ℝ) (hq : 1 ≤ q) :
    fkc_u d s q n ≤ ((ecz_T m n) ^ d : ℝ) * fkc_u d s q m
      + (((boxGraph d n).edgeFinset.card : ℝ)
          - ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ))
          * (-Real.log (1 - fsc_logistic s)) := by
  classical
  set p := fsc_logistic s with hp
  have hp0 : (0 : ℝ) < p := fsc_logistic_pos s
  have hp1 : p < 1 := fsc_logistic_lt_one s
  set c := -Real.log (1 - p) with hc
  set tag := ecz_vanHoveTag m n with htag
  set K₀ := boxGraph d n with hK₀
  have hsub := ecz_multiblock_subadd K₀ tag p q hp0 hp1 (by linarith) Finset.univ
  have hrest_u : ecz_uu (qp_restG K₀ tag Finset.univ) p q = fkc_u d s q n := by
    rw [ecz_uu, fkc_u, hp, ecz_fkZEdge_iso (ecz_restUnivIso m n) p q]
  have hrest_E : ((qp_restG K₀ tag Finset.univ).edgeFinset.card : ℝ)
      = ((boxGraph d n).edgeFinset.card : ℝ) := by
    rw [(ecz_restUnivIso m n).card_edgeFinset_eq]
  have hsplit_u : (∑ τ : Option (Fin d → Fin (ecz_T m n)), ecz_uu (qp_blkG K₀ tag τ) p q)
      = ecz_uu (qp_blkG K₀ tag none) p q
        + ((ecz_T m n) ^ d : ℝ) * fkc_u d s q m := by
    rw [Fintype.sum_option]
    congr 1
    have heach : ∀ a : Fin d → Fin (ecz_T m n),
        ecz_uu (qp_blkG K₀ tag (some a)) p q = fkc_u d s q m := fun a => by
      rw [ecz_uu, fkc_u, hp, ecz_cellBlock_fkZEdge m n a]
    rw [Finset.sum_congr rfl (fun a _ => heach a), Finset.sum_const, Finset.card_univ,
      ecz_cell_card, nsmul_eq_mul]
    push_cast; ring
  have hsplit_E : (∑ τ : Option (Fin d → Fin (ecz_T m n)),
        ((qp_blkG K₀ tag τ).edgeFinset.card : ℝ))
      = ((qp_blkG K₀ tag none).edgeFinset.card : ℝ)
        + ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ) := by
    rw [Fintype.sum_option]
    congr 1
    have heach : ∀ a : Fin d → Fin (ecz_T m n),
        ((qp_blkG K₀ tag (some a)).edgeFinset.card : ℝ)
          = ((boxGraph d m).edgeFinset.card : ℝ) := fun a => by
      rw [ecz_cellBlock_edge_card m n a]
    rw [Finset.sum_congr rfl (fun a _ => heach a), Finset.sum_const, Finset.card_univ,
      ecz_cell_card, nsmul_eq_mul]
    push_cast; ring
  have hnone : ecz_uu (qp_blkG K₀ tag none) p q
      ≤ ((qp_blkG K₀ tag none).edgeFinset.card : ℝ) * c := by
    rw [ecz_uu, hc]
    exact ecz_neglogZEdge_le_edges _ hp0 hp1 hq
  rw [show (∑ τ ∈ (Finset.univ : Finset (Option (Fin d → Fin (ecz_T m n)))),
        ecz_uu (qp_blkG K₀ tag τ) p q)
      = ∑ τ : Option (Fin d → Fin (ecz_T m n)), ecz_uu (qp_blkG K₀ tag τ) p q from rfl]
    at hsub
  rw [show (∑ τ ∈ (Finset.univ : Finset (Option (Fin d → Fin (ecz_T m n)))),
        ((qp_blkG K₀ tag τ).edgeFinset.card : ℝ))
      = ∑ τ : Option (Fin d → Fin (ecz_T m n)),
          ((qp_blkG K₀ tag τ).edgeFinset.card : ℝ) from rfl] at hsub
  rw [hrest_u, hsplit_u, hrest_E, hsplit_E] at hsub
  set uNone : ℝ := ecz_uu (qp_blkG K₀ tag none) p q
  set ENone : ℝ := ((qp_blkG K₀ tag none).edgeFinset.card : ℝ)
  set Td : ℝ := ((ecz_T m n) ^ d : ℝ)
  set Um : ℝ := fkc_u d s q m
  set Em : ℝ := ((boxGraph d m).edgeFinset.card : ℝ)
  set En : ℝ := ((boxGraph d n).edgeFinset.card : ℝ)
  have hexpand : (En - (ENone + Td * Em)) * c = (En - Td * Em) * c - ENone * c := by ring
  rw [hexpand] at hsub
  linarith [hsub, hnone]


theorem fkc_perEdge_vanHove (d m n : ℕ) (s q : ℝ) (hq : 1 ≤ q)
    (hEn : 0 < (boxGraph d n).edgeFinset.card) (hEm : 0 < (boxGraph d m).edgeFinset.card) :
    fkc_f d s q n
      ≤ (((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ)
            / ((boxGraph d n).edgeFinset.card : ℝ)) * fkc_f d s q m
        + (1 - ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ)
            / ((boxGraph d n).edgeFinset.card : ℝ)) * (-Real.log (1 - fsc_logistic s)) := by
  have hEnR : (0 : ℝ) < ((boxGraph d n).edgeFinset.card : ℝ) := by exact_mod_cast hEn
  have hEmR : (0 : ℝ) < ((boxGraph d m).edgeFinset.card : ℝ) := by exact_mod_cast hEm
  have hsub := fkc_box_vanHove_subadd d m n s q hq
  rw [fkc_f, fkc_f]
  set En : ℝ := ((boxGraph d n).edgeFinset.card : ℝ)
  set Em : ℝ := ((boxGraph d m).edgeFinset.card : ℝ)
  set Td : ℝ := ((ecz_T m n) ^ d : ℝ)
  set c : ℝ := -Real.log (1 - fsc_logistic s)
  rw [div_le_iff₀ hEnR]
  have hkey : (Td * Em / En * (fkc_u d s q m / Em) + (1 - Td * Em / En) * c) * En
      = Td * fkc_u d s q m + (En - Td * Em) * c := by field_simp
  calc fkc_u d s q n ≤ Td * fkc_u d s q m + (En - Td * Em) * c := hsub
    _ = (Td * Em / En * (fkc_u d s q m / Em) + (1 - Td * Em / En) * c) * En := hkey.symm


end StatMech.Walls

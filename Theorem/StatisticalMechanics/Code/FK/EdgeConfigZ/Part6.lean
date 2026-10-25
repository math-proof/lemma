/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.SuperMultiplicative.Part4
import Theorem.StatisticalMechanics.Code.FK.FKInterfaceSubadd.Part2
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
import Theorem.StatisticalMechanics.Code.FK.CenteredFreeEnergy.Part3
import Theorem.StatisticalMechanics.Code.FK.BoxFeketePerVolume.Part2
import Def.StatisticalMechanics.Code.FK.EdgeConfigZ.Part6
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

namespace FK

open StatMech.Lattice


section AdditiveDoubling

variable {d : ℕ}


theorem ecz_additiveDoublingBound (d : ℕ) (hd : 1 ≤ d) (t : ℝ) :
    ecz_AdditiveDoublingBound d t := by
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
  · apply qp_summable_ratio d hd I _ hInn
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
  · intro j
    have hdbl := ecz_box_neglog_doubling d (agl_K j) t
    rw [show ecz_u d t (agl_K (j + 1)) = ecz_u d t (2 * agl_K j + 1) from by rw [agl_K_succ]]
    have hge : N j * c ≤ I j * c := by
      rw [hI]; apply mul_le_mul_of_nonneg_right _ hc0; linarith [hGnn j]
    calc ecz_u d t (2 * agl_K j + 1)
        ≤ (2 : ℝ) ^ d * ecz_u d t (agl_K j) + N j * c := hdbl
      _ ≤ (2 : ℝ) ^ d * ecz_u d t (agl_K j) + I j * c := by linarith
  · intro j
    have hGval : G j = agl_E d (agl_K (j + 1)) - (2 : ℝ) ^ d * agl_E d (agl_K j) := rfl
    rw [abs_of_nonpos (by have := hGnn j; rw [hGval] at this; linarith)]
    rw [hI]; have hNn : 0 ≤ N j := Nat.cast_nonneg _
    have hGeq : -((2 : ℝ) ^ d * agl_E d (agl_K j) - agl_E d (agl_K (j + 1))) = G j := by
      rw [hGval]; ring
    rw [hGeq]; linarith

end AdditiveDoubling


section Boundedness

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem ecz_numClusters_le (ω : ConfigSpace (Sym2 V)) : numClusters G ω ≤ Fintype.card V := by
  unfold numClusters
  apply Fintype.card_le_of_surjective (openSub G ω).connectedComponentMk
  intro c
  induction c using SimpleGraph.ConnectedComponent.ind with
  | _ v => exact ⟨v, rfl⟩


theorem ecz_fkWeight_le {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (ω : ConfigSpace (Sym2 V)) :
    fkWeight G p 2 ω ≤ 2 ^ Fintype.card V := by
  unfold fkWeight
  have hep : edgeProduct G p ω ≤ 1 := by
    unfold edgeProduct
    apply Finset.prod_le_one
    · intro e _; split <;> [exact hp.le; linarith]
    · intro e _; split <;> [exact hp1.le; linarith]
  have hq : (2:ℝ) ^ numClusters G ω ≤ 2 ^ Fintype.card V :=
    pow_le_pow_right₀ (by norm_num) (ecz_numClusters_le G ω)
  calc edgeProduct G p ω * 2 ^ numClusters G ω
      ≤ 1 * 2 ^ Fintype.card V := by
        exact mul_le_mul hep hq (by positivity) (by norm_num)
    _ = 2 ^ Fintype.card V := by ring


theorem ecz_closedOff_card : Fintype.card (ecz_ClosedOff G) = 2 ^ G.edgeFinset.card := by
  classical
  rw [show (2:ℕ) ^ G.edgeFinset.card = Fintype.card (G.edgeFinset → Bool) from by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]]
  apply Fintype.card_congr
  refine ⟨fun ω e => ω.val e.val,
    fun η => ⟨fun e => if h : e ∈ G.edgeFinset then η ⟨e, h⟩ else false,
      fun e he => by simp only [dif_neg he]⟩, ?_, ?_⟩
  · intro ω; apply Subtype.ext; funext e
    by_cases he : e ∈ G.edgeFinset
    · simp only [dif_pos he]
    · simp only [dif_neg he]; exact (ω.2 e he).symm
  · intro η; funext e; simp only [dif_pos e.2]


theorem ecz_fkZEdge_le {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    ecz_fkZEdge G p 2 ≤ (2 : ℝ) ^ G.edgeFinset.card * 2 ^ Fintype.card V := by
  unfold ecz_fkZEdge
  calc ∑ ω : ecz_ClosedOff G, fkWeight G p 2 ω.val
      ≤ ∑ ω : ecz_ClosedOff G, (2:ℝ) ^ Fintype.card V :=
        Finset.sum_le_sum (fun ω _ => ecz_fkWeight_le G hp hp1 ω.val)
    _ = (Fintype.card (ecz_ClosedOff G) : ℝ) * 2 ^ Fintype.card V := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (2 : ℝ) ^ G.edgeFinset.card * 2 ^ Fintype.card V := by
        rw [ecz_closedOff_card G]; push_cast; ring

end Boundedness


section BoxBounds


theorem ecz_box_edge_pos (d : ℕ) (hd : 1 ≤ d) {n : ℕ} (hn : 1 ≤ n) :
    0 < (boxGraph d n).edgeFinset.card := by
  rw [EdgeCount.boxGraph_edgeCard d n hd]
  have hdp : 0 < d := hd
  have hnp : 0 < 2 * n := by omega
  have hpow : 0 < (2 * n + 1) ^ (d - 1) := pow_pos (by omega) _
  positivity


theorem ecz_boxVerts_card (d n : ℕ) : Fintype.card (boxVerts d n) = (2 * n + 1) ^ d := by
  rw [← boxSV_card_boxF d n]
  apply Fintype.card_of_subtype (boxSV_boxF d n)
  intro x
  rw [boxSV_mem_boxF]
  show (∀ i, x i ∈ Finset.Icc (-(n:ℤ)) n) ↔ x ∈ box d n
  rw [mem_box]
  refine forall_congr' (fun i => ?_)
  rw [Finset.mem_Icc]
  constructor
  · intro ⟨h1, h2⟩; omega
  · intro h; constructor <;> omega


theorem ecz_boxVerts_le_edges (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    Fintype.card (boxVerts d n) ≤ 2 * (boxGraph d n).edgeFinset.card := by
  rw [ecz_boxVerts_card, EdgeCount.boxGraph_edgeCard d n hd]
  have hd1 : (2 * n + 1) ^ d = (2 * n + 1) * (2 * n + 1) ^ (d - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [hd1]
  calc (2 * n + 1) * (2 * n + 1) ^ (d - 1)
      ≤ (2 * (d * (2 * n))) * (2 * n + 1) ^ (d - 1) := by
        apply Nat.mul_le_mul_right
        nlinarith [hd, hn]
    _ = 2 * (d * (2 * n * (2 * n + 1) ^ (d - 1))) := by ring


theorem ecz_edgeFE_le_const (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (s : ℝ)
    (hE : 0 < (boxGraph d n).edgeFinset.card) :
    ecz_edgeFreeEnergy d s n ≤ 3 * Real.log 2 + Real.log (1 + Real.exp s) := by
  unfold ecz_edgeFreeEnergy ecz_u
  set E := (boxGraph d n).edgeFinset.card with hEdef
  set V := Fintype.card (boxVerts d n) with hVdef
  set p := fsc_logistic s
  have hp0 : (0:ℝ) < p := fsc_logistic_pos s
  have hp1 : p < 1 := fsc_logistic_lt_one s
  have hEr : (0:ℝ) < (E:ℝ) := by exact_mod_cast hE
  have hZpos : 0 < ecz_fkZEdge (boxGraph d n) p 2 := ecz_fkZEdge_pos _ hp0 hp1 (by norm_num)
  have hub : ecz_fkZEdge (boxGraph d n) p 2 ≤ (2:ℝ)^E * 2^V := ecz_fkZEdge_le _ hp0 hp1
  have hlog : Real.log (ecz_fkZEdge (boxGraph d n) p 2) ≤ ((E:ℝ) + V) * Real.log 2 := by
    calc Real.log (ecz_fkZEdge (boxGraph d n) p 2)
        ≤ Real.log ((2:ℝ)^E * 2^V) := Real.log_le_log hZpos hub
      _ = (E:ℝ) * Real.log 2 + V * Real.log 2 := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
      _ = ((E:ℝ) + V) * Real.log 2 := by ring
  have hVle : (V:ℝ) ≤ 2 * E := by exact_mod_cast ecz_boxVerts_le_edges d n hd hn
  have hlog2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hkey : -(-Real.log (ecz_fkZEdge (boxGraph d n) p 2) / (E:ℝ)) ≤ 3 * Real.log 2 := by
    rw [neg_div, neg_neg, div_le_iff₀ hEr]
    calc Real.log (ecz_fkZEdge (boxGraph d n) p 2) ≤ ((E:ℝ) + V) * Real.log 2 := hlog
      _ ≤ ((E:ℝ) + 2 * E) * Real.log 2 := by
          apply mul_le_mul_of_nonneg_right _ hlog2; linarith
      _ = 3 * Real.log 2 * E := by ring
  linarith

end BoxBounds
end FK
end StatMech

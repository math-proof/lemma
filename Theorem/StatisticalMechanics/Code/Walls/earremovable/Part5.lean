/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Theorem.StatisticalMechanics.Code.Walls.nbcnoncut.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc_leafremoval.Part2
import Theorem.StatisticalMechanics.Code.Walls.atcattachstep.Part2
import Def.StatisticalMechanics.Code.Walls.earremovable.Part4
open Finset Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


theorem ear_adj_rightCell (b : Site 2) : (hypercubicLattice 2).Adj b (ear_rightCell b) := by
  rw [ear_rightCell, hypercubicLattice_adj, Fin.sum_univ_two]; simp [Pi.add_apply]

theorem ear_adj_upCell (b : Site 2) : (hypercubicLattice 2).Adj b (ear_upCell b) := by
  rw [ear_upCell, hypercubicLattice_adj, Fin.sum_univ_two]; simp [Pi.add_apply]


theorem ear_antiExtreme_neighbor_rightCell_or_upCell (K : Set (Site 2)) (b v : Site 2)
    (hb : ear_IsAntiExtreme K b) (hv : v ∈ K) (hadj : (hypercubicLattice 2).Adj b v) :
    v = ear_rightCell b ∨ v = ear_upCell b := by
  rcases adj_neighbor_cases v b hadj.symm with h | h | h | h
  · exact Or.inl h
  · exact absurd (h ▸ hv) (ear_antiExtreme_left_nmem K b hb)
  · exact Or.inr h
  · exact absurd (h ▸ hv) (ear_antiExtreme_down_nmem K b hb)


theorem ear_antiExtreme_pendant_of_up_nmem {K : Finset (Site 2)} (hcard : 2 ≤ K.card)
    (hconn : IsConnectedCluster K) {b : Site 2} (hb : ear_IsAntiExtreme (↑K : Set (Site 2)) b)
    (hup : ear_upCell b ∉ (↑K : Set (Site 2))) :
    jc_IsPendantCell (↑K : Set (Site 2)) b := by
  classical
  obtain ⟨v, hvK, hadj⟩ := ear_exists_neighbor_of_conn hcard hconn (by exact_mod_cast hb.mem)
  have hvK' : v ∈ (↑K : Set (Site 2)) := by exact_mod_cast hvK
  refine ⟨hb.mem, ear_rightCell b, ⟨?_, ear_adj_rightCell b⟩, ?_⟩
  · rcases ear_antiExtreme_neighbor_rightCell_or_upCell (↑K : Set (Site 2)) b v hb hvK' hadj with
      h | h
    · rw [← h]; exact hvK'
    · exact absurd (h ▸ hvK') hup
  · rintro w ⟨hwK, hwadj⟩
    rcases ear_antiExtreme_neighbor_rightCell_or_upCell (↑K : Set (Site 2)) b w hb hwK hwadj with
      h | h
    · exact h
    · exact absurd (h ▸ hwK) hup


theorem ear_antiExtreme_pendant_of_right_nmem {K : Finset (Site 2)} (hcard : 2 ≤ K.card)
    (hconn : IsConnectedCluster K) {b : Site 2} (hb : ear_IsAntiExtreme (↑K : Set (Site 2)) b)
    (hright : ear_rightCell b ∉ (↑K : Set (Site 2))) :
    jc_IsPendantCell (↑K : Set (Site 2)) b := by
  classical
  obtain ⟨v, hvK, hadj⟩ := ear_exists_neighbor_of_conn hcard hconn (by exact_mod_cast hb.mem)
  have hvK' : v ∈ (↑K : Set (Site 2)) := by exact_mod_cast hvK
  refine ⟨hb.mem, ear_upCell b, ⟨?_, ear_adj_upCell b⟩, ?_⟩
  · rcases ear_antiExtreme_neighbor_rightCell_or_upCell (↑K : Set (Site 2)) b v hb hvK' hadj with
      h | h
    · exact absurd (h ▸ hvK') hright
    · rw [← h]; exact hvK'
  · rintro w ⟨hwK, hwadj⟩
    rcases ear_antiExtreme_neighbor_rightCell_or_upCell (↑K : Set (Site 2)) b w hb hwK hwadj with
      h | h
    · exact absurd (h ▸ hwK) hright
    · exact h


theorem ear_gKey_injective : Function.Injective ear_gKey := by
  intro a b h
  unfold ear_gKey at h
  
  have h' : (a 1, a 0) = (b 1, b 0) := h
  rw [Prod.mk.injEq] at h'
  obtain ⟨h1, h0⟩ := h'
  funext i; fin_cases i <;> assumption


theorem ear_extremes_distinct {K : Finset (Site 2)} (hcard : 2 ≤ K.card) {c b : Site 2}
    (hc : ear_IsGlobalExtreme (↑K : Set (Site 2)) c)
    (hb : ear_IsAntiExtreme (↑K : Set (Site 2)) b) :
    c ≠ b := by
  classical
  intro hcb
  subst hcb
  
  have hall : ∀ v ∈ (↑K : Set (Site 2)), v = c := by
    intro v hv
    have h1 := hc.maximal v hv
    have h2 := hb.minimal v hv
    exact ear_gKey_injective (le_antisymm h1 h2)
  
  have hsub : K ⊆ {c} := by
    intro x hx
    rw [Finset.mem_singleton]
    exact hall x (by exact_mod_cast hx)
  have := Finset.card_le_card hsub
  simp at this; omega


theorem ear_removable_of_antiPendant_ne_origin {K : Finset (Site 2)}
    (hconn : IsConnectedCluster K) {b : Site 2} (hb : ear_IsAntiExtreme (↑K : Set (Site 2)) b)
    (hborigin : b ≠ origin 2) (hpend : jc_IsPendantCell (↑K : Set (Site 2)) b) :
    ∃ d ∈ K, d ≠ origin 2 ∧ (∃ n ∉ K, (hypercubicLattice 2).Adj d n) ∧
      CellConnected ((↑K : Set (Site 2)) \ {d}) := by
  refine ⟨b, by exact_mod_cast hb.mem, hborigin,
    ear_antiExtreme_boundary (↑K : Set (Site 2)) b hb, ?_⟩
  exact jc_cellConnected_diff_of_pendant (↑K : Set (Site 2)) b
    (nbc_cellConnected_of_isConnectedCluster hconn) hpend


theorem ear_globalExtreme_dichotomy {K : Finset (Site 2)} (hcard : 2 ≤ K.card)
    (hconn : IsConnectedCluster K) {c : Site 2} (hc : ear_IsGlobalExtreme (↑K : Set (Site 2)) c)
    (hcorigin : c ≠ origin 2) :
    (∃ d ∈ K, d ≠ origin 2 ∧ (∃ n ∉ K, (hypercubicLattice 2).Adj d n) ∧
        CellConnected ((↑K : Set (Site 2)) \ {d}))
      ∨ (ear_leftCell c ∈ (↑K : Set (Site 2)) ∧ ear_downCell c ∈ (↑K : Set (Site 2))) := by
  classical
  by_cases hp : ear_leftCell c ∈ (↑K : Set (Site 2))
  · by_cases hq : ear_downCell c ∈ (↑K : Set (Site 2))
    · exact Or.inr ⟨hp, hq⟩
    · exact Or.inl (ear_removable_of_pendant_ne_origin hconn hc hcorigin
        (ear_globalExtreme_pendant_of_down_nmem hcard hconn hc hq))
  · exact Or.inl (ear_removable_of_pendant_ne_origin hconn hc hcorigin
      (ear_globalExtreme_pendant_of_left_nmem hcard hconn hc hp))


theorem ear_antiExtreme_dichotomy {K : Finset (Site 2)} (hcard : 2 ≤ K.card)
    (hconn : IsConnectedCluster K) {b : Site 2} (hb : ear_IsAntiExtreme (↑K : Set (Site 2)) b)
    (hborigin : b ≠ origin 2) :
    (∃ d ∈ K, d ≠ origin 2 ∧ (∃ n ∉ K, (hypercubicLattice 2).Adj d n) ∧
        CellConnected ((↑K : Set (Site 2)) \ {d}))
      ∨ (ear_rightCell b ∈ (↑K : Set (Site 2)) ∧ ear_upCell b ∈ (↑K : Set (Site 2))) := by
  classical
  by_cases hr : ear_rightCell b ∈ (↑K : Set (Site 2))
  · by_cases hu : ear_upCell b ∈ (↑K : Set (Site 2))
    · exact Or.inr ⟨hr, hu⟩
    · exact Or.inl (ear_removable_of_antiPendant_ne_origin hconn hb hborigin
        (ear_antiExtreme_pendant_of_up_nmem hcard hconn hb hu))
  · exact Or.inl (ear_removable_of_antiPendant_ne_origin hconn hb hborigin
      (ear_antiExtreme_pendant_of_right_nmem hcard hconn hb hr))


theorem ear_boundaryNonCut_of_pendantExtreme {K : Finset (Site 2)} (_hcard : 2 ≤ K.card)
    (hconn : IsConnectedCluster K)
    (hpend : (∃ c, ear_IsGlobalExtreme (↑K : Set (Site 2)) c ∧ c ≠ origin 2 ∧
                jc_IsPendantCell (↑K : Set (Site 2)) c)
           ∨ (∃ b, ear_IsAntiExtreme (↑K : Set (Site 2)) b ∧ b ≠ origin 2 ∧
                jc_IsPendantCell (↑K : Set (Site 2)) b)) :
    ∃ d ∈ K, d ≠ origin 2 ∧ (∃ n ∉ K, (hypercubicLattice 2).Adj d n) ∧
      CellConnected ((↑K : Set (Site 2)) \ {d}) := by
  rcases hpend with ⟨c, hc, hco, hp⟩ | ⟨b, hb, hbo, hp⟩
  · exact ear_removable_of_pendant_ne_origin hconn hc hco hp
  · exact ear_removable_of_antiPendant_ne_origin hconn hb hbo hp


theorem ear_cutWitness_globalExtreme : ear_IsGlobalExtreme cutWitness ![2, 1] := by
  refine ⟨cw_v21, ?_⟩
  intro v hv
  rw [mem_cutWitness] at hv
  unfold ear_gKey
  rcases hv with h | h | h | h <;> subst h <;> rw [Prod.Lex.toLex_le_toLex] <;> simp


theorem ear_cutWitness_globalExtreme_pendant : jc_IsPendantCell cutWitness ![2, 1] := by
  classical
  refine ⟨cw_v21, ![1, 1], ⟨cw_v11, ?_⟩, ?_⟩
  · rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  · rintro w ⟨hwK, hadj⟩
    rw [mem_cutWitness] at hwK
    rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
    rcases hwK with h | h | h | h <;> subst h <;> revert hadj <;> decide


theorem ear_cutWitness_removable : CellConnected (cutWitness \ {![2, 1]}) :=
  jc_cellConnected_diff_of_pendant cutWitness ![2, 1] cutWitness_cellConnected
    ear_cutWitness_globalExtreme_pendant


theorem ear_tromino_globalExtreme : ear_IsGlobalExtreme (↑pc2_tromino : Set (Site 2)) ![0, 1] := by
  refine ⟨by rw [pc2_mem_tromino]; tauto, ?_⟩
  intro v hv
  obtain ⟨p, q, rfl⟩ : ∃ p q, v = ![p, q] := ⟨v 0, v 1, by funext i; fin_cases i <;> rfl⟩
  rw [pc2_mem_tromino] at hv
  unfold ear_gKey
  rcases hv with ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩ <;> subst hp <;> subst hq <;>
    rw [Prod.Lex.toLex_le_toLex] <;> simp


theorem ear_tromino_antiExtreme : ear_IsAntiExtreme (↑pc2_tromino : Set (Site 2)) ![0, 0] := by
  refine ⟨by rw [pc2_mem_tromino]; tauto, ?_⟩
  intro v hv
  obtain ⟨p, q, rfl⟩ : ∃ p q, v = ![p, q] := ⟨v 0, v 1, by funext i; fin_cases i <;> rfl⟩
  rw [pc2_mem_tromino] at hv
  unfold ear_gKey
  rcases hv with ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩ <;> subst hp <;> subst hq <;>
    rw [Prod.Lex.toLex_le_toLex] <;> simp


theorem ear_tromino_nonvacuous :
    ∃ c ∈ pc2_tromino, c ≠ origin 2 ∧
      (∃ n ∉ pc2_tromino, (hypercubicLattice 2).Adj c n) ∧
      CellConnected ((↑pc2_tromino : Set (Site 2)) \ {c}) := by
  classical
  have hne : (![0, 1] : Site 2) ≠ origin 2 := by
    rw [origin_eq_zerozero]; intro h; have := congrFun h 1; simp at this
  
  have hpend : jc_IsPendantCell (↑pc2_tromino : Set (Site 2)) ![0, 1] := by
    refine ⟨by rw [pc2_mem_tromino]; tauto, ![0, 0], ⟨by rw [pc2_mem_tromino]; tauto, ?_⟩, ?_⟩
    · rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
    · rintro w ⟨hwK, hadj⟩
      obtain ⟨p, q, rfl⟩ : ∃ p q, w = ![p, q] := ⟨w 0, w 1, by funext i; fin_cases i <;> rfl⟩
      rw [pc2_mem_tromino] at hwK
      rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
      rcases hwK with ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩ <;> subst hp <;> subst hq <;>
        revert hadj <;> decide
  refine ⟨![0, 1], by rw [← Finset.mem_coe, pc2_mem_tromino]; tauto, hne,
    ?_, ?_⟩
  · obtain ⟨n, hn, hadj⟩ := ear_globalExtreme_boundary (↑pc2_tromino : Set (Site 2)) ![0, 1]
      ear_tromino_globalExtreme
    exact ⟨n, fun hc => hn (Finset.mem_coe.mpr hc), hadj⟩
  exact jc_cellConnected_diff_of_pendant (↑pc2_tromino : Set (Site 2)) ![0, 1]
    (nbc_cellConnected_of_isConnectedCluster pc2_tromino_isConnectedCluster) hpend

end Walls
end StatMech

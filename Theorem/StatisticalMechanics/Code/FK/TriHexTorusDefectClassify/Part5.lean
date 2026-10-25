/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexTorusDuality.Part10
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusConnected
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.EulerComponentCount.Part2
import Instance.StatisticalMechanics.Code.FK.TriHexTorusDefectClassify
open Finset Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

open StatMech.Lattice

open StatMech.Onsager

@[simp] theorem triHexTorusPrimalOfDualEdge_indexed
    (L : ℕ) [Fact (2 < L)] (a : TriHexTorusEdgeIndex L) :
    triHexTorusPrimalOfDualEdge L (hexagonalTorusIndexedEdge L a) =
      triangularTorusIndexedEdge L ((triHexTorusIndexEquiv L).symm a) := by
  have he : hexagonalTorusIndexedEdge L a ∈
      (hexagonalTorusGraph L).edgeSet := hexagonalTorusIndexedEdge_mem L a
  simp only [triHexTorusPrimalOfDualEdge, dif_pos he]
  change (((triHexTorusDualEdgeEquiv L).symm
      (hexagonalTorusEdgeChart L a) :
        (triangularTorusGraph L).edgeSet) : Sym2 (TorusSite L)) = _
  rw [show hexagonalTorusEdgeChart L a =
      hexagonalTorusEdgeChartEquiv L a by rfl]
  simp [triHexTorusDualEdgeEquiv, triangularTorusEdgeChartEquiv,
    hexagonalTorusEdgeChartEquiv, triangularTorusEdgeChart]

@[simp] theorem triHexTorusPrimalOfDualEdge_index_zero
    (L : ℕ) [Fact (2 < L)] (z : TorusSite L) :
    triHexTorusPrimalOfDualEdge L
        (hexagonalTorusIndexedEdge L (z, 0)) =
      s(z, z + (1, 0)) := by
  rw [triHexTorusPrimalOfDualEdge_indexed]
  rfl

@[simp] theorem triHexTorusPrimalOfDualEdge_index_one
    (L : ℕ) [Fact (2 < L)] (z : TorusSite L) :
    triHexTorusPrimalOfDualEdge L
        (hexagonalTorusIndexedEdge L (z, 1)) =
      s(z, z + (0, 1)) := by
  rw [triHexTorusPrimalOfDualEdge_indexed]
  rfl

@[simp] theorem triHexTorusPrimalOfDualEdge_index_two
    (L : ℕ) [Fact (2 < L)] (z : TorusSite L) :
    triHexTorusPrimalOfDualEdge L
        (hexagonalTorusIndexedEdge L (z, 2)) =
      s(z + (1, 0), z + (0, 1)) := by
  rw [triHexTorusPrimalOfDualEdge_indexed]
  change s(z + (1, 0), z + (1, 0) + (-1, 1)) = _
  congr 1
  ext <;> simp


theorem hexagonalTorusGraph_adj_black_iff
    (L : ℕ) [Fact (2 < L)] (z : TorusSite L) (w : HexTorusVertex L) :
    (hexagonalTorusGraph L).Adj (z, false) w ↔
      ∃ i : Fin 3, w = (z + hexagonalTorusStep L i, true) := by
  constructor
  · rintro ⟨⟨a, i⟩, h⟩
    rw [hexagonalTorusIndexedEdge, Sym2.eq_iff] at h
    rcases h with h | h
    · have ha : a = z := congrArg Prod.fst h.1
      subst a
      exact ⟨i, h.2.symm⟩
    · have hf : (true : Bool) = false := congrArg Prod.snd h.2
      simp at hf
  · rintro ⟨i, rfl⟩
    exact ⟨(z, i), rfl⟩


theorem hexagonalTorusGraph_adj_white_iff
    (L : ℕ) [Fact (2 < L)] (z : TorusSite L) (w : HexTorusVertex L) :
    (hexagonalTorusGraph L).Adj (z, true) w ↔
      ∃ i : Fin 3, w = (z - hexagonalTorusStep L i, false) := by
  constructor
  · rintro ⟨⟨a, i⟩, h⟩
    rw [hexagonalTorusIndexedEdge, Sym2.eq_iff] at h
    rcases h with h | h
    · have hf : (false : Bool) = true := congrArg Prod.snd h.1
      simp at hf
    · have hz : a + hexagonalTorusStep L i = z :=
        congrArg Prod.fst h.2
      refine ⟨i, ?_⟩
      apply Prod.ext
      · have ha : a = z - hexagonalTorusStep L i :=
          (eq_sub_iff_add_eq).2 hz
        exact (congrArg Prod.fst h.1).symm.trans ha
      · simpa using congrArg Prod.snd h.1
  · rintro ⟨i, rfl⟩
    refine ⟨(z - hexagonalTorusStep L i, i), ?_⟩
    rw [hexagonalTorusIndexedEdge, Sym2.eq_swap]
    congr 1
    ext <;> simp


theorem hexagonalTorusGraph_neighborFinset_black
    (L : ℕ) [Fact (2 < L)] (z : TorusSite L) :
    (hexagonalTorusGraph L).neighborFinset (z, false) =
      {(z + (1, 0), true), (z + (0, 1), true),
        (z + (1, 1), true)} := by
  ext w
  rw [SimpleGraph.mem_neighborFinset, hexagonalTorusGraph_adj_black_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [hexagonalTorusStep]
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by simp [hexagonalTorusStep]⟩
    · exact ⟨1, by simp [hexagonalTorusStep]⟩
    · exact ⟨2, by simp [hexagonalTorusStep]⟩


theorem hexagonalTorusGraph_neighborFinset_white
    (L : ℕ) [Fact (2 < L)] (z : TorusSite L) :
    (hexagonalTorusGraph L).neighborFinset (z, true) =
      {(z - (1, 0), false), (z - (0, 1), false),
        (z - (1, 1), false)} := by
  ext w
  rw [SimpleGraph.mem_neighborFinset, hexagonalTorusGraph_adj_white_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [hexagonalTorusStep]
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by simp [hexagonalTorusStep]⟩
    · exact ⟨1, by simp [hexagonalTorusStep]⟩
    · exact ⟨2, by simp [hexagonalTorusStep]⟩


@[simp] theorem triHexTorusPrimalOfDualEdge_white_zero
    (L : ℕ) [Fact (2 < L)] (z : TorusSite L) :
    triHexTorusPrimalOfDualEdge L
        s((z, true), (z - (1, 0), false)) =
      s(z - (1, 0), z) := by
  rw [Sym2.eq_swap]
  rw [show s((z - (1, 0), false), (z, true)) =
      hexagonalTorusIndexedEdge L (z - (1, 0), 0) by
    unfold hexagonalTorusIndexedEdge
    congr 1
    ext <;> simp [hexagonalTorusStep]]
  rw [triHexTorusPrimalOfDualEdge_index_zero]
  congr 1
  ext <;> simp

@[simp] theorem triHexTorusPrimalOfDualEdge_white_one
    (L : ℕ) [Fact (2 < L)] (z : TorusSite L) :
    triHexTorusPrimalOfDualEdge L
        s((z, true), (z - (0, 1), false)) =
      s(z - (0, 1), z) := by
  rw [Sym2.eq_swap]
  rw [show s((z - (0, 1), false), (z, true)) =
      hexagonalTorusIndexedEdge L (z - (0, 1), 1) by
    unfold hexagonalTorusIndexedEdge
    congr 1
    ext <;> simp [hexagonalTorusStep]]
  rw [triHexTorusPrimalOfDualEdge_index_one]
  congr 1
  ext <;> simp

@[simp] theorem triHexTorusPrimalOfDualEdge_white_two
    (L : ℕ) [Fact (2 < L)] (z : TorusSite L) :
    triHexTorusPrimalOfDualEdge L
        s((z, true), (z - (1, 1), false)) =
      s(z - (0, 1), z - (1, 0)) := by
  rw [Sym2.eq_swap]
  rw [show s((z - (1, 1), false), (z, true)) =
      hexagonalTorusIndexedEdge L (z - (1, 1), 2) by
    unfold hexagonalTorusIndexedEdge
    congr 1
    ext <;> simp [hexagonalTorusStep]]
  rw [triHexTorusPrimalOfDualEdge_index_two]
  congr 1 <;> ext <;> simp

@[simp] theorem triHexTorusPrimalOfDualEdge_black_zero
    (L : ℕ) [Fact (2 < L)] (z : TorusSite L) :
    triHexTorusPrimalOfDualEdge L
        s((z, false), (z + (1, 0), true)) =
      s(z, z + (1, 0)) := by
  rw [show s((z, false), (z + (1, 0), true)) =
      hexagonalTorusIndexedEdge L (z, 0) by
    unfold hexagonalTorusIndexedEdge
    congr 1]
  exact triHexTorusPrimalOfDualEdge_index_zero L z

@[simp] theorem triHexTorusPrimalOfDualEdge_black_one
    (L : ℕ) [Fact (2 < L)] (z : TorusSite L) :
    triHexTorusPrimalOfDualEdge L
        s((z, false), (z + (0, 1), true)) =
      s(z, z + (0, 1)) := by
  rw [show s((z, false), (z + (0, 1), true)) =
      hexagonalTorusIndexedEdge L (z, 1) by
    unfold hexagonalTorusIndexedEdge
    congr 1]
  exact triHexTorusPrimalOfDualEdge_index_one L z

@[simp] theorem triHexTorusPrimalOfDualEdge_black_two
    (L : ℕ) [Fact (2 < L)] (z : TorusSite L) :
    triHexTorusPrimalOfDualEdge L
        s((z, false), (z + (1, 1), true)) =
      s(z + (1, 0), z + (0, 1)) := by
  rw [show s((z, false), (z + (1, 1), true)) =
      hexagonalTorusIndexedEdge L (z, 2) by
    unfold hexagonalTorusIndexedEdge
    congr 1]
  exact triHexTorusPrimalOfDualEdge_index_two L z


theorem triHexTorusCutDualGraph_degree_even
    (L : ℕ) [Fact (2 < L)] (S : Set (TorusSite L))
    (v : HexTorusVertex L) :
    Even ((triHexTorusCutDualGraph L S).degree v) := by
  classical
  have hfilter : (triHexTorusCutDualGraph L S).neighborFinset v =
      ((hexagonalTorusGraph L).neighborFinset v).filter (fun w =>
        triHexTorusEdgeStraddles S
          (triHexTorusPrimalOfDualEdge L s(v, w))) := by
    ext w
    simp [triHexTorusCutDualGraph_adj]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hfilter]
  rcases v with ⟨z, b⟩
  cases b with
  | false =>
      rw [hexagonalTorusGraph_neighborFinset_black]
      have h1 : (1 : ZMod L) ≠ 0 := triHex_zmod_one_ne_zero L
      have h01 : (z + (1, 0), true) ≠ (z + (0, 1), true) := by
        intro h
        apply h1
        have hf : z.1 + 1 = z.1 + 0 := by
          simpa using congrArg (fun x => x.1.1) h
        exact add_left_cancel hf
      have h02 : (z + (1, 0), true) ≠ (z + (1, 1), true) := by
        intro h
        apply h1
        have hs : z.2 + 0 = z.2 + 1 := by
          simpa using congrArg (fun x => x.1.2) h
        exact (add_left_cancel hs).symm
      have h12 : (z + (0, 1), true) ≠ (z + (1, 1), true) := by
        intro h
        apply h1
        have hf : z.1 + 0 = z.1 + 1 := by
          simpa using congrArg (fun x => x.1.1) h
        exact (add_left_cancel hf).symm
      by_cases hz : z ∈ S <;>
      by_cases hx : z + (1, 0) ∈ S <;>
      by_cases hy : z + (0, 1) ∈ S <;>
        simp [Finset.filter_insert, Finset.filter_singleton,
          triHexTorusEdgeStraddles_mk, hz, hx, hy, h01, h02, h12]
  | true =>
      rw [hexagonalTorusGraph_neighborFinset_white]
      have h1 : (1 : ZMod L) ≠ 0 := triHex_zmod_one_ne_zero L
      have h01 : (z - (1, 0), false) ≠ (z - (0, 1), false) := by
        intro h
        apply h1
        have hf : z.1 - 1 = z.1 - 0 := by
          simpa using congrArg (fun x => x.1.1) h
        exact sub_right_inj.mp hf
      have h02 : (z - (1, 0), false) ≠ (z - (1, 1), false) := by
        intro h
        apply h1
        have hs : z.2 - 0 = z.2 - 1 := by
          simpa using congrArg (fun x => x.1.2) h
        exact (sub_right_inj.mp hs).symm
      have h12 : (z - (0, 1), false) ≠ (z - (1, 1), false) := by
        intro h
        apply h1
        have hf : z.1 - 0 = z.1 - 1 := by
          simpa using congrArg (fun x => x.1.1) h
        exact (sub_right_inj.mp hf).symm
      by_cases hz : z ∈ S <;>
      by_cases hx : z - (1, 0) ∈ S <;>
      by_cases hy : z - (0, 1) ∈ S <;>
        simp [Finset.filter_insert, Finset.filter_singleton,
          triHexTorusEdgeStraddles_mk, hz, hx, hy, h01, h02, h12]


end PeriodicPlanar
end FK
end StatMech

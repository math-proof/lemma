/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePotential.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusFaceBoundary
import Theorem.StatisticalMechanics.Code.Onsager.TorusPrimitiveWinding.Part3
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusFacePotential.Part2
open scoped BigOperators
open scoped symmDiff


namespace StatMech.FrontierA

open StatMech.Onsager

theorem mem_image_east_iff
    (L : Nat) [Fact (2 < L)]
    (S : Finset (ZMod L × ZMod L)) (p : ZMod L × ZMod L) :
    ons_portEdge L (p, 0) ∈ S.image (fun q => ons_portEdge L (q, 0)) ↔
      p ∈ S := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨q, hq, heq⟩
    exact (ons_eastPortEdge_injective L heq).symm ▸ hq
  · intro hp
    exact ⟨p, hp, rfl⟩

theorem mem_image_north_iff
    (L : Nat) [Fact (2 < L)]
    (S : Finset (ZMod L × ZMod L)) (p : ZMod L × ZMod L) :
    ons_portEdge L (p, 1) ∈ S.image (fun q => ons_portEdge L (q, 1)) ↔
      p ∈ S := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨q, hq, heq⟩
    exact (ons_northPortEdge_injective L heq).symm ▸ hq
  · intro hp
    exact ⟨p, hp, rfl⟩

theorem mem_shifted_image_north_iff
    (L : Nat) [Fact (2 < L)]
    (S : Finset (ZMod L × ZMod L)) (p : ZMod L × ZMod L) :
    ons_portEdge L (p, 1) ∈
        S.image (fun q => ons_portEdge L ((q.1 + 1, q.2), 1)) ↔
      (p.1 - 1, p.2) ∈ S := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨q, hq, heq⟩
    have hsite := ons_northPortEdge_injective L heq
    have hqsite : q = (p.1 - 1, p.2) := by
      apply Prod.ext
      · have hx := congrArg Prod.fst hsite
        dsimp at hx
        linear_combination hx
      · simpa using congrArg Prod.snd hsite
    rwa [hqsite] at hq
  · intro hp
    refine ⟨(p.1 - 1, p.2), hp, ?_⟩
    apply congrArg (fun q => ons_portEdge L (q, 1))
    apply Prod.ext <;> simp <;> ring

theorem east_not_mem_verticalEdges
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L))) (p : ZMod L × ZMod L) :
    ons_portEdge L (p, 0) ∉ triangularSquareVerticalEdges L F := by
  intro hmem
  rw [triangularSquareVerticalEdges, Finset.mem_symmDiff] at hmem
  rcases hmem with ⟨hmem, -⟩ | ⟨hmem, -⟩
  · rw [Finset.mem_image] at hmem
    obtain ⟨q, -, heq⟩ := hmem
    exact ons_eastPortEdge_ne_northPortEdge L p q heq.symm
  · rw [Finset.mem_image] at hmem
    obtain ⟨q, -, heq⟩ := hmem
    exact ons_eastPortEdge_ne_northPortEdge L p (q.1 + 1, q.2) heq.symm

theorem north_not_mem_horizontalEdges
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L))) (p : ZMod L × ZMod L) :
    ons_portEdge L (p, 1) ∉ triangularSquareHorizontalEdges L F := by
  intro hmem
  rw [triangularSquareHorizontalEdges, Finset.mem_symmDiff] at hmem
  rcases hmem with ⟨hmem, -⟩ | ⟨hmem, -⟩
  · rw [Finset.mem_image] at hmem
    obtain ⟨q, -, heq⟩ := hmem
    exact ons_eastPortEdge_ne_northPortEdge L q p heq
  · rw [Finset.mem_image] at hmem
    obtain ⟨q, -, heq⟩ := hmem
    exact ons_eastPortEdge_ne_northPortEdge L q p heq

theorem triangularSquareExpansion_horizontalBit
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L))) (p : ZMod L × ZMod L) :
    ons_horizontalZBit (triangularSquareExpansion L F) p =
      (ons_edgeBit F (triangularTorusEastEdge L p) : ZMod 2) +
        (ons_edgeBit F (triangularTorusNortheastEdge L p) : ZMod 2) := by
  have hH : ons_portEdge L (p, 0) ∈
      triangularSquareHorizontalEdges L F ↔
      (triangularTorusEastEdge L p ∈ F ∧
          triangularTorusNortheastEdge L p ∉ F) ∨
        (triangularTorusNortheastEdge L p ∈ F ∧
          triangularTorusEastEdge L p ∉ F) := by
    unfold triangularSquareHorizontalEdges
    rw [Finset.mem_symmDiff, mem_image_east_iff, mem_image_east_iff]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hV := east_not_mem_verticalEdges L F p
  unfold ons_horizontalZBit ons_horizontalBit triangularSquareExpansion
  rw [ons_edgeBit]
  simp only [Finset.mem_union, hV, or_false, hH]
  by_cases he : triangularTorusEastEdge L p ∈ F <;>
    by_cases hd : triangularTorusNortheastEdge L p ∈ F <;>
      simp [ons_edgeBit, he, hd]

theorem triangularSquareExpansion_verticalBit
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L))) (p : ZMod L × ZMod L) :
    ons_verticalZBit (triangularSquareExpansion L F) p =
      (ons_edgeBit F (triangularTorusNorthEdge L p) : ZMod 2) +
        (ons_edgeBit F
          (triangularTorusNortheastEdge L (p.1 - 1, p.2)) : ZMod 2) := by
  have hV : ons_portEdge L (p, 1) ∈ triangularSquareVerticalEdges L F ↔
      (triangularTorusNorthEdge L p ∈ F ∧
          triangularTorusNortheastEdge L (p.1 - 1, p.2) ∉ F) ∨
        (triangularTorusNortheastEdge L (p.1 - 1, p.2) ∈ F ∧
          triangularTorusNorthEdge L p ∉ F) := by
    unfold triangularSquareVerticalEdges
    rw [Finset.mem_symmDiff, mem_image_north_iff,
      mem_shifted_image_north_iff]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hH := north_not_mem_horizontalEdges L F p
  unfold ons_verticalZBit ons_verticalBit triangularSquareExpansion
  rw [ons_edgeBit]
  simp only [Finset.mem_union, hH, false_or, hV]
  by_cases hn : triangularTorusNorthEdge L p ∈ F <;>
    by_cases hd : triangularTorusNortheastEdge L (p.1 - 1, p.2) ∈ F <;>
      simp [ons_edgeBit, hn, hd]

theorem triangularSquareExpansion_subset_edgeFinset
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L))) :
    triangularSquareExpansion L F ⊆ (onsTorusGraph L).edgeFinset := by
  intro edge hedge
  rw [triangularSquareExpansion, Finset.mem_union] at hedge
  rcases hedge with hedge | hedge
  · rw [triangularSquareHorizontalEdges, Finset.mem_symmDiff] at hedge
    rcases hedge with ⟨hedge, -⟩ | ⟨hedge, -⟩ <;>
      rw [Finset.mem_image] at hedge <;>
      obtain ⟨p, -, rfl⟩ := hedge <;>
      exact ons_portEdge_mem_edgeFinset L (p, 0)
  · rw [triangularSquareVerticalEdges, Finset.mem_symmDiff] at hedge
    rcases hedge with ⟨hedge, -⟩ | ⟨hedge, -⟩ <;>
      rw [Finset.mem_image] at hedge
    · obtain ⟨p, -, rfl⟩ := hedge
      exact ons_portEdge_mem_edgeFinset L (p, 1)
    · obtain ⟨p, -, rfl⟩ := hedge
      exact ons_portEdge_mem_edgeFinset L ((p.1 + 1, p.2), 1)

set_option maxHeartbeats 800000 in


theorem triangularSquareExpansion_evenSubgraph
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ StatMech.Ising.evenSubgraphs (triangularTorusGraph L)) :
    triangularSquareExpansion L F ∈
      StatMech.Ising.evenSubgraphs (onsTorusGraph L) := by
  let E := triangularSquareExpansion L F
  have hsubset : E ⊆ (onsTorusGraph L).edgeFinset :=
    triangularSquareExpansion_subset_edgeFinset L F
  rw [StatMech.Ising.evenSubgraphs, Finset.mem_filter,
    Finset.mem_powerset]
  refine ⟨hsubset, ?_⟩
  intro p
  have hEeq : E = (onsTorusGraph L).edgeFinset.filter (fun e => e ∈ E) := by
    ext edge
    simp only [Finset.mem_filter]
    constructor
    · intro hedge
      exact ⟨hsubset hedge, hedge⟩
    · exact And.right
  have hcast := ons_cast_incCount_filter_eq_neighbor_sum
    (onsTorusGraph L) (fun e => e ∈ E) p
  rw [← hEeq, ons_torus_neighbor_sum_eq_direction_sum] at hcast
  rw [Fin.sum_univ_four] at hcast
  have hzero :
      ons_horizontalZBit E p +
        ons_horizontalZBit E (p.1 - 1, p.2) +
        ons_verticalZBit E p +
        ons_verticalZBit E (p.1, p.2 - 1) = 0 := by
    dsimp [E]
    rw [triangularSquareExpansion_horizontalBit,
      triangularSquareExpansion_horizontalBit,
      triangularSquareExpansion_verticalBit,
      triangularSquareExpansion_verticalBit]
    have hdiv := triangularTorus_edgeBits_divergence_zero L F hF p
    let d : Fin 2 := ons_edgeBit F
      (triangularTorusNortheastEdge L (p.1 - 1, p.2))
    have hdd : d + d = 0 := by
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_zero]
      omega
    calc
      _ = (ons_edgeBit F (triangularTorusEastEdge L p) +
              ons_edgeBit F
                (triangularTorusEastEdge L (p.1 - 1, p.2)) +
              ons_edgeBit F (triangularTorusNorthEdge L p) +
              ons_edgeBit F
                (triangularTorusNorthEdge L (p.1, p.2 - 1)) +
              ons_edgeBit F (triangularTorusNortheastEdge L p) +
              ons_edgeBit F (triangularTorusNortheastEdge L
                (p.1 - 1, p.2 - 1))) + (d + d) := by
        dsimp [d]
        abel
      _ = ons_edgeBit F (triangularTorusEastEdge L p) +
              ons_edgeBit F
                (triangularTorusEastEdge L (p.1 - 1, p.2)) +
              ons_edgeBit F (triangularTorusNorthEdge L p) +
              ons_edgeBit F
                (triangularTorusNorthEdge L (p.1, p.2 - 1)) +
              ons_edgeBit F (triangularTorusNortheastEdge L p) +
              ons_edgeBit F (triangularTorusNortheastEdge L
                (p.1 - 1, p.2 - 1)) := by
        rw [hdd, add_zero]
      _ = 0 := hdiv
  have hcastzero : ((StatMech.Ising.incCount E p : Nat) : ZMod 2) = 0 := by
    change ((StatMech.Ising.incCount E p : Nat) : ZMod 2) =
      ((if ons_portEdge L (p, 0) ∈ E then 1 else 0) +
        (if ons_portEdge L (p, 1) ∈ E then 1 else 0) +
        (if ons_portEdge L (p, 2) ∈ E then 1 else 0) +
        if ons_portEdge L (p, 3) ∈ E then 1 else 0) at hcast
    rw [ons_portEdge_west_eq_horizontal,
      ons_portEdge_south_eq_vertical] at hcast
    rw [hcast]
    simpa only [ons_horizontalZBit, ons_horizontalBit,
      ons_verticalZBit, ons_verticalBit, ons_edgeBit,
      add_assoc, add_left_comm, add_comm] using hzero
  rw [Nat.even_iff]
  exact Nat.mod_eq_zero_of_dvd
    ((CharP.cast_eq_zero_iff (ZMod 2) 2 _).mp hcastzero)

end StatMech.FrontierA

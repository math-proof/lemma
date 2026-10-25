/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWSequentialStoppedExplorationBridge
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorSeededMassCapstone.Part2
import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEquiv.Part2
import Theorem.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part3
import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxDomainMarkov.Part3
import Def.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw.Part10
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorFoldRight_adj {x y : Site 2}
    (hxy : (hypercubicLattice 2).Adj x y) :
    (hypercubicLattice 2).Adj
      (rlc_connectorFoldRight x) (rlc_connectorFoldRight y) := by
  by_cases hx : 0 ≤ x 0 <;> by_cases hy : 0 ≤ y 0 <;>
    simp [rlc_connectorFoldRight, hx, hy, rlc_flipX, rlc_flipXFun,
      hypercubicLattice_adj, Fin.sum_univ_two] at hxy ⊢ <;> omega

theorem rlc_connectorFoldLeft_adj {x y : Site 2}
    (hxy : (hypercubicLattice 2).Adj x y) :
    (hypercubicLattice 2).Adj
      (rlc_connectorFoldLeft x) (rlc_connectorFoldLeft y) := by
  by_cases hx : x 0 ≤ 0 <;> by_cases hy : y 0 ≤ 0 <;>
    simp [rlc_connectorFoldLeft, hx, hy, rlc_flipX, rlc_flipXFun,
      hypercubicLattice_adj, Fin.sum_univ_two] at hxy ⊢ <;> omega

theorem rlc_connectorFoldRight_mem_rect {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {z : Site 2} (hz : z ∈ rlc_connectorAllowed gamma gamma') :
    rlc_connectorFoldRight z ∈ rect 0 (2 * n) (-n) n := by
  have hzBox := (Finset.mem_sdiff.mp hz).1
  rw [rlc_connectorBox, Set.Finite.mem_toFinset, mem_rect] at hzBox
  by_cases hz0 : 0 ≤ z 0
  · rw [rlc_connectorFoldRight, if_pos hz0, mem_rect]
    exact ⟨hz0, hzBox.2⟩
  · simp [rlc_connectorFoldRight, hz0, rlc_flipX, rlc_flipXFun,
      mem_rect]
    omega

theorem rlc_connectorFoldLeft_mem_rect {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {z : Site 2} (hz : z ∈ rlc_connectorAllowed gamma gamma') :
    rlc_connectorFoldLeft z ∈ rect (-2 * n) 0 (-n) n := by
  have hzBox := (Finset.mem_sdiff.mp hz).1
  rw [rlc_connectorBox, Set.Finite.mem_toFinset, mem_rect] at hzBox
  by_cases hz0 : z 0 ≤ 0
  · rw [rlc_connectorFoldLeft, if_pos hz0, mem_rect]
    exact ⟨hzBox.1, hz0, hzBox.2.2⟩
  · simp [rlc_connectorFoldLeft, hz0, rlc_flipX, rlc_flipXFun,
      mem_rect]
    omega

theorem rlc_connectorFoldRight_not_path {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {z : Site 2} (hz : z ∈ rlc_connectorAllowed gamma gamma') :
    rlc_connectorFoldRight z ∉ rlc_pathVertices gamma.1 := by
  have hzNotBarrier := (Finset.mem_sdiff.mp hz).2
  by_cases hz0 : 0 ≤ z 0
  · rw [rlc_connectorFoldRight, if_pos hz0]
    intro hzPath
    apply hzNotBarrier
    rw [rlc_connectorBarrier]
    simp only [Finset.mem_union]
    exact Or.inl (Or.inl (Or.inl hzPath))
  · rw [rlc_connectorFoldRight, if_neg hz0]
    intro hzPath
    apply hzNotBarrier
    rw [rlc_connectorBarrier]
    simp only [Finset.mem_union]
    apply Or.inl
    apply Or.inr
    exact Finset.mem_image.mpr
      ⟨rlc_flipX z, hzPath, rlc_flipX_involutive z⟩

theorem rlc_connectorFoldLeft_not_path {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {z : Site 2} (hz : z ∈ rlc_connectorAllowed gamma gamma') :
    rlc_connectorFoldLeft z ∉ rlc_pathVertices gamma'.1 := by
  have hzNotBarrier := (Finset.mem_sdiff.mp hz).2
  by_cases hz0 : z 0 ≤ 0
  · rw [rlc_connectorFoldLeft, if_pos hz0]
    intro hzPath
    apply hzNotBarrier
    rw [rlc_connectorBarrier]
    simp only [Finset.mem_union]
    exact Or.inl (Or.inl (Or.inr hzPath))
  · rw [rlc_connectorFoldLeft, if_neg hz0]
    intro hzPath
    apply hzNotBarrier
    rw [rlc_connectorBarrier]
    simp only [Finset.mem_union]
    apply Or.inr
    exact Finset.mem_image.mpr
      ⟨rlc_flipX z, hzPath, rlc_flipX_involutive z⟩


end
end StatMech.Universality

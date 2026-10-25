/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInternalCylinderLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalPlusCorrDecay
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeInternalCylinderLimit.Part2
open MeasureTheory Filter Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness StatMech.Lattice

noncomputable section

theorem oddCubicalCenteredSite_internalCentralCellEmbedding
    (n m : Nat) (hnm : centralSquareSide n < m)
    (q : CubicalCell (centralSquareSide n) (centralSquareSide n)
      (centralSquareSide n + centralSquareSide n)) :
    oddCubicalCenteredSite m (internalCentralCellEmbedding n m hnm q) =
      centralCylinderSite n q := by
  funext i
  fin_cases i
  · simp [centralCylinderSite, internalCentralCellEmbedding]
  · simp [centralCylinderSite, internalCentralCellEmbedding]
  · simp [centralCylinderSite, internalCentralCellEmbedding]
    have hle : centralSquareSide n <= m := hnm.le
    simp only [Nat.cast_add, Nat.cast_sub hle]
    ring


theorem cubicalDualL1_internalCentralVertexEmbedding
    (n m : Nat) (hnm : centralSquareSide n < m)
    (u v : CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
      (centralSquareSide n + centralSquareSide n)) :
    cubicalDualL1 (internalCentralVertexEmbedding n m hnm u)
        (internalCentralVertexEmbedding n m hnm v) =
      cubicalDualL1 u v := by
  cases u with
  | none => rfl
  | some q =>
    cases v with
    | none => rfl
    | some r =>
      simp only [internalCentralVertexEmbedding_some, cubicalDualL1,
        internalCentralCellEmbedding]
      change
        Nat.dist (m + q.x.val) (m + r.x.val) +
            Nat.dist (m + q.y.val) (m + r.y.val) +
              Nat.dist (m - centralSquareSide n + q.z.val)
                (m - centralSquareSide n + r.z.val) =
          Nat.dist q.x.val r.x.val + Nat.dist q.y.val r.y.val +
            Nat.dist q.z.val r.z.val
      rw [Nat.dist_add_add_left, Nat.dist_add_add_left,
        Nat.dist_add_add_left]


theorem mem_centralLowerBoundaryVertices_iff
    (n : Nat)
    (q : CubicalCell (centralSquareSide n) (centralSquareSide n)
      (centralSquareSide n + centralSquareSide n)) :
    some q ∈ centralLowerBoundaryVertices n ↔
      q.z.val < centralSquareSide n ∧
        (q.x.val = 0 ∨ q.x.val + 1 = centralSquareSide n ∨
         q.y.val = 0 ∨ q.y.val + 1 = centralSquareSide n ∨
         q.z.val = 0) := by
  simp [centralLowerBoundaryVertices, centralLowerBottomVertices,
    centralLowerWestVertices, centralLowerEastVertices,
    centralLowerSouthVertices, centralLowerNorthVertices]
  constructor
  · intro h
    rcases h with h | h | h | h | h
    all_goals rcases h with ⟨i, j, h⟩
    all_goals subst q
    all_goals simp [centralSquareSide] at *
    · exact Or.inr (Or.inr (Or.inr (Or.inr (by
        apply Fin.ext
        simp))))
    all_goals omega
  · rintro ⟨hz, h⟩
    rcases q with ⟨x, y, z⟩
    simp only at hz h ⊢
    rcases h with hx | hx | hy | hy | hz0
    · exact Or.inr (Or.inl ⟨y, ⟨z.val, by
        simpa [centralSquareSide] using hz⟩, by
        rw [CubicalCell.mk.injEq]
        refine ⟨hx.symm, rfl, ?_⟩
        apply Fin.ext
        rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨y, ⟨z.val, by
        simpa [centralSquareSide] using hz⟩, by
        rw [CubicalCell.mk.injEq]
        refine ⟨?_, rfl, ?_⟩
        · apply Fin.ext
          simpa [centralSquareSide] using hx.symm
        · apply Fin.ext
          rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨x, ⟨z.val, by simpa [centralSquareSide] using hz⟩, by
          rw [CubicalCell.mk.injEq]
          refine ⟨rfl, hy.symm, ?_⟩
          apply Fin.ext
          rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨x, ⟨z.val, by simpa [centralSquareSide] using hz⟩, by
          rw [CubicalCell.mk.injEq]
          refine ⟨rfl, ?_, ?_⟩
          · apply Fin.ext
            simpa [centralSquareSide] using hy.symm
          · apply Fin.ext
            rfl⟩)))
    · exact Or.inl ⟨x, y, by
        rw [CubicalCell.mk.injEq]
        refine ⟨rfl, rfl, ?_⟩
        simpa using hz0.symm⟩


theorem centralLowerBoundaryVertices_map_internal
    (n m : Nat) (hnm : centralSquareSide n < m) :
    (centralLowerBoundaryVertices n).map
        (internalCentralVertexEmbedding n m hnm) =
      cubicalInternalCentralBoundaryVertices (centralSquareSide n) m := by
  ext v
  constructor
  · intro hv
    obtain ⟨u, hu, huv⟩ := Finset.mem_map.mp hv
    cases u with
    | none =>
        exact (none_not_mem_centralLowerBoundaryVertices n hu).elim
    | some q =>
        subst v
        have hq := (mem_centralLowerBoundaryVertices_iff n q).mp hu
        apply Finset.mem_image.mpr
        refine ⟨internalCentralCellEmbedding n m hnm q, ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        change
          m <= m + q.x.val ∧
          m + q.x.val < m + centralSquareSide n ∧
          m <= m + q.y.val ∧
          m + q.y.val < m + centralSquareSide n ∧
          m - centralSquareSide n <=
            m - centralSquareSide n + q.z.val ∧
          m - centralSquareSide n + q.z.val < m ∧
          (m + q.x.val = m ∨
           m + q.x.val + 1 = m + centralSquareSide n ∨
           m + q.y.val = m ∨
           m + q.y.val + 1 = m + centralSquareSide n ∨
           m - centralSquareSide n + q.z.val =
             m - centralSquareSide n)
        rcases hq with ⟨hz, hboundary⟩
        have hle : centralSquareSide n <= m := hnm.le
        refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
        rcases hboundary with hx0 | hx1 | hy0 | hy1 | hz0
        · exact Or.inl (by omega)
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr (Or.inl (by omega)))
        · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (by omega))))
  · intro hv
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hv
    have hcoord := (Finset.mem_filter.mp hq).2
    let x : Fin (centralSquareSide n) :=
      ⟨q.x.val - m, by omega⟩
    let y : Fin (centralSquareSide n) :=
      ⟨q.y.val - m, by omega⟩
    let z : Fin (centralSquareSide n + centralSquareSide n) :=
      ⟨q.z.val - (m - centralSquareSide n), by
        dsimp [centralSquareSide] at *
        omega⟩
    let r : CubicalCell (centralSquareSide n) (centralSquareSide n)
        (centralSquareSide n + centralSquareSide n) :=
      CubicalCell.mk x y z
    apply Finset.mem_map.mpr
    refine ⟨some r, ?_, ?_⟩
    · rw [mem_centralLowerBoundaryVertices_iff]
      dsimp [r, x, y, z]
      refine ⟨by omega, ?_⟩
      rcases hcoord.2.2.2.2.2.2 with hx0 | hx1 | hy0 | hy1 | hz0
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr (Or.inl (by omega)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (by omega))))
    · simp only [internalCentralVertexEmbedding_some, Option.some.injEq]
      rw [CubicalCell.mk.injEq]
      refine ⟨?_, ?_, ?_⟩
      · apply Fin.ext
        dsimp [internalCentralCellEmbedding, r, x]
        omega
      · apply Fin.ext
        dsimp [internalCentralCellEmbedding, r, y]
        omega
      · apply Fin.ext
        dsimp [internalCentralCellEmbedding, r, z]
        omega


theorem centralUpperLayerVertices_map_internal
    (n m : Nat) (hnm : centralSquareSide n < m) :
    (centralUpperLayerVertices n).map
        (internalCentralVertexEmbedding n m hnm) =
      cubicalInternalCentralUpperCoordinateVertices
        (centralSquareSide n) m hnm.le := by
  ext v
  constructor
  · intro hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hv
    cases u with
    | none => exact (none_not_mem_centralUpperLayerVertices n hu).elim
    | some q =>
        obtain ⟨ij, _, hq⟩ := Finset.mem_image.mp hu
        simp only [Option.some.injEq] at hq
        subst q
        apply Finset.mem_image.mpr
        refine ⟨ij, Finset.mem_univ _, ?_⟩
        simp only [internalCentralVertexEmbedding_some, Option.some.injEq]
        rw [CubicalCell.mk.injEq]
        refine ⟨?_, ?_, ?_⟩
        · apply Fin.ext
          rfl
        · apply Fin.ext
          rfl
        · apply Fin.ext
          dsimp [internalCentralCellEmbedding]
          exact (Nat.sub_add_cancel hnm.le).symm
  · intro hv
    obtain ⟨ij, _, rfl⟩ := Finset.mem_image.mp hv
    let q : CubicalCell (centralSquareSide n) (centralSquareSide n)
        (centralSquareSide n + centralSquareSide n) :=
      CubicalCell.mk ij.1 ij.2
        ⟨centralSquareSide n, by
          dsimp [centralSquareSide]
          omega⟩
    apply Finset.mem_map.mpr
    refine ⟨some q, ?_, ?_⟩
    · apply Finset.mem_image.mpr
      refine ⟨ij, Finset.mem_univ _, ?_⟩
      apply congrArg some
      rw [CubicalCell.mk.injEq]
      exact ⟨rfl, rfl, Fin.ext rfl⟩
    · simp only [internalCentralVertexEmbedding_some, Option.some.injEq]
      rw [CubicalCell.mk.injEq]
      refine ⟨?_, ?_, ?_⟩
      · apply Fin.ext
        rfl
      · apply Fin.ext
        rfl
      · apply Fin.ext
        dsimp [internalCentralCellEmbedding, q]
        exact Nat.sub_add_cancel hnm.le


end
end StatMech.FrontierA

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialRectangle.Part6
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDirichletLimit.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialPatch.Part10


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open Filter Set Topology

noncomputable section

theorem fkIsingSquareRadialPatchPrimalNodeVertex_injective
    (n m : Nat) (hm : m ≤ n) :
    Function.Injective (fkIsingSquareRadialPatchPrimalNodeVertex n m hm) := by
  intro p q hpq
  have h0 := congrArg (fun u : (fkSquareBoxPlanar n).V ↦ u.1 0) hpq
  have h1 := congrArg (fun u : (fkSquareBoxPlanar n).V ↦ u.1 1) hpq
  simp [fkIsingSquareRadialPatchPrimalNodeVertex,
    fkIsingSquareRadialPatchVertex] at h0 h1
  have hpmod : (p.1.1.1 + p.1.2.1) % 2 = 0 := Nat.even_iff.mp p.2
  have hqmod : (q.1.1.1 + q.1.2.1) % 2 = 0 := Nat.even_iff.mp q.2
  have hpcoord : 2 * fkIsingSquareRadialPatchHalf p.1.1.1 p.1.2.1 =
      p.1.1.1 + p.1.2.1 := by
    unfold fkIsingSquareRadialPatchHalf
    omega
  have hqcoord : 2 * fkIsingSquareRadialPatchHalf q.1.1.1 q.1.2.1 =
      q.1.1.1 + q.1.2.1 := by
    unfold fkIsingSquareRadialPatchHalf
    omega
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext <;> omega


theorem fkIsingSquareRadialPatchVertex_northeast_eq_neighbor_east
    (n m i j : Nat) (hm : m ≤ n)
    (hi : i + 1 < m) (hj : j + 1 < m) (heven : Even (i + j)) :
    fkIsingSquareRadialPatchVertex n m hm
        ⟨i + 1, hi⟩ ⟨j + 1, hj⟩ =
      fkIsingSquareNeighbor n
        (fkIsingSquareRadialPatchVertex n m hm
          ⟨i, by omega⟩ ⟨j, by omega⟩)
        .east (by
          have h := fkIsingSquareRadialPatchDirection_available n m hm
            ⟨i, by omega⟩ ⟨j, by omega⟩
          simpa [fkIsingSquareRadialPatchDirection, heven] using h) := by
  apply Subtype.ext
  funext k
  fin_cases k <;>
    simp [fkIsingSquareRadialPatchVertex, fkIsingSquareRadialPatchHalf,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite, Pi.add_apply]
  · have hmod := Nat.even_iff.mp heven
    omega
  · have hmod := Nat.even_iff.mp heven
    omega


theorem fkIsingSquareRadialPatchVertex_northwest_eq_neighbor_north
    (n m i j : Nat) (hm : m ≤ n)
    (hi : i + 1 < m) (hj0 : 0 < j) (hj : j < m)
    (heven : Even (i + j)) :
    fkIsingSquareRadialPatchVertex n m hm
        ⟨i + 1, hi⟩ ⟨j - 1, by omega⟩ =
      fkIsingSquareNeighbor n
        (fkIsingSquareRadialPatchVertex n m hm
          ⟨i, by omega⟩ ⟨j, by omega⟩)
        .north (by
          simp [fkIsingSquareDirectionAvailable,
            fkIsingSquareRadialPatchVertex, fkIsingSquareRadialPatchHalf]
          have hmod := Nat.even_iff.mp heven
          omega) := by
  have hjcast : ((j - 1 : Nat) : Int) = (j : Int) - 1 := by omega
  apply Subtype.ext
  funext k
  fin_cases k <;>
    simp [fkIsingSquareRadialPatchVertex, fkIsingSquareRadialPatchHalf,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite, Pi.add_apply, hjcast]
  · have hmod := Nat.even_iff.mp heven
    omega


theorem fkIsingSquareRadialPatchVertex_southwest_eq_neighbor_west
    (n m i j : Nat) (hm : m ≤ n)
    (hi0 : 0 < i) (hj0 : 0 < j) (hi : i < m) (hj : j < m)
    (heven : Even (i + j)) :
    fkIsingSquareRadialPatchVertex n m hm
        ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ =
      fkIsingSquareNeighbor n
        (fkIsingSquareRadialPatchVertex n m hm ⟨i, hi⟩ ⟨j, hj⟩)
        .west (by
          simp [fkIsingSquareDirectionAvailable,
            fkIsingSquareRadialPatchVertex, fkIsingSquareRadialPatchHalf]
          have hmod := Nat.even_iff.mp heven
          omega) := by
  have hhalf :
      fkIsingSquareRadialPatchHalf (i - 1) (j - 1) + 1 =
        fkIsingSquareRadialPatchHalf i j := by
    unfold fkIsingSquareRadialPatchHalf
    have hmod := Nat.even_iff.mp heven
    omega
  have hhalfInt :
      (fkIsingSquareRadialPatchHalf (i - 1) (j - 1) : Int) + 1 =
        (fkIsingSquareRadialPatchHalf i j : Int) := by
    exact_mod_cast hhalf
  have hicast : ((i - 1 : Nat) : Int) = (i : Int) - 1 := by omega
  apply Subtype.ext
  funext k
  fin_cases k
  · simp [fkIsingSquareRadialPatchVertex, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite]
    omega
  · simp [fkIsingSquareRadialPatchVertex, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite]
    omega


theorem fkIsingSquareRadialPatchVertex_southeast_eq_neighbor_south
    (n m i j : Nat) (hm : m ≤ n)
    (hi0 : 0 < i) (hj : j + 1 < m) (hi : i < m)
    (heven : Even (i + j)) :
    fkIsingSquareRadialPatchVertex n m hm
        ⟨i - 1, by omega⟩ ⟨j + 1, hj⟩ =
      fkIsingSquareNeighbor n
        (fkIsingSquareRadialPatchVertex n m hm
          ⟨i, hi⟩ ⟨j, by omega⟩)
        .south (by
          simp [fkIsingSquareDirectionAvailable,
            fkIsingSquareRadialPatchVertex, fkIsingSquareRadialPatchHalf]
          have hmod := Nat.even_iff.mp heven
          omega) := by
  have hhalf : fkIsingSquareRadialPatchHalf (i - 1) (j + 1) =
      fkIsingSquareRadialPatchHalf i j := by
    unfold fkIsingSquareRadialPatchHalf
    have hmod := Nat.even_iff.mp heven
    omega
  have hhalfInt : (fkIsingSquareRadialPatchHalf (i - 1) (j + 1) : Int) =
      (fkIsingSquareRadialPatchHalf i j : Int) := by
    exact_mod_cast hhalf
  have hicast : ((i - 1 : Nat) : Int) = (i : Int) - 1 := by omega
  apply Subtype.ext
  funext k
  fin_cases k <;>
    simp [fkIsingSquareRadialPatchVertex, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite] <;> omega


theorem fkIsingSquareRadialPatch_adj_iff_diagonal
    (n m i j : Nat) (hm : m ≤ n)
    (hi0 : 0 < i) (hi1 : i + 1 < m)
    (hj0 : 0 < j) (hj1 : j + 1 < m)
    (heven : Even (i + j)) (y : (fkSquareBoxPlanar n).V) :
    (fkSquareBoxPlanar n).G.Adj
        (fkIsingSquareRadialPatchVertex n m hm
          ⟨i, by omega⟩ ⟨j, by omega⟩) y ↔
      y = fkIsingSquareRadialPatchVertex n m hm
          ⟨i + 1, hi1⟩ ⟨j + 1, hj1⟩ ∨
      y = fkIsingSquareRadialPatchVertex n m hm
          ⟨i + 1, hi1⟩ ⟨j - 1, by omega⟩ ∨
      y = fkIsingSquareRadialPatchVertex n m hm
          ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ ∨
      y = fkIsingSquareRadialPatchVertex n m hm
          ⟨i - 1, by omega⟩ ⟨j + 1, hj1⟩ := by
  let c := fkIsingSquareRadialPatchVertex n m hm
    ⟨i, by omega⟩ ⟨j, by omega⟩
  have heast : fkIsingSquareDirectionAvailable n c .east := by
    have h := fkIsingSquareRadialPatchDirection_available n m hm
      ⟨i, by omega⟩ ⟨j, by omega⟩
    simpa [c, fkIsingSquareRadialPatchDirection, heven] using h
  have hnorth : fkIsingSquareDirectionAvailable n c .north := by
    simp [c, fkIsingSquareDirectionAvailable,
      fkIsingSquareRadialPatchVertex, fkIsingSquareRadialPatchHalf]
    have hmod := Nat.even_iff.mp heven
    omega
  have hwest : fkIsingSquareDirectionAvailable n c .west := by
    simp [c, fkIsingSquareDirectionAvailable,
      fkIsingSquareRadialPatchVertex, fkIsingSquareRadialPatchHalf]
    have hmod := Nat.even_iff.mp heven
    omega
  have hsouth : fkIsingSquareDirectionAvailable n c .south := by
    simp [c, fkIsingSquareDirectionAvailable,
      fkIsingSquareRadialPatchVertex, fkIsingSquareRadialPatchHalf]
    have hmod := Nat.even_iff.mp heven
    omega
  have hNE :
      fkIsingSquareRadialPatchVertex n m hm
          ⟨i + 1, hi1⟩ ⟨j + 1, hj1⟩ =
        fkIsingSquareNeighbor n c .east heast := by
    simpa only [c] using
      fkIsingSquareRadialPatchVertex_northeast_eq_neighbor_east
        n m i j hm hi1 hj1 heven
  have hNW :
      fkIsingSquareRadialPatchVertex n m hm
          ⟨i + 1, hi1⟩ ⟨j - 1, by omega⟩ =
        fkIsingSquareNeighbor n c .north hnorth := by
    simpa only [c] using
      fkIsingSquareRadialPatchVertex_northwest_eq_neighbor_north
        n m i j hm hi1 hj0 (by omega) heven
  have hSW :
      fkIsingSquareRadialPatchVertex n m hm
          ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ =
        fkIsingSquareNeighbor n c .west hwest := by
    simpa only [c] using
      fkIsingSquareRadialPatchVertex_southwest_eq_neighbor_west
        n m i j hm hi0 hj0 (by omega) (by omega) heven
  have hSE :
      fkIsingSquareRadialPatchVertex n m hm
          ⟨i - 1, by omega⟩ ⟨j + 1, hj1⟩ =
        fkIsingSquareNeighbor n c .south hsouth := by
    simpa only [c] using
      fkIsingSquareRadialPatchVertex_southeast_eq_neighbor_south
        n m i j hm hi0 hj1 (by omega) heven
  constructor
  · intro hadj
    change NearestNeighbour 2 c.1 y.1 at hadj
    rw [nearestNeighbour_iff_shift] at hadj
    obtain ⟨k, s, hs, hy⟩ := hadj
    fin_cases k <;> rcases hs with rfl | rfl
    · left
      rw [hNE]
      apply Subtype.ext
      funext l
      have hyl := congrFun hy l
      fin_cases l <;>
        simpa [fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
          shift, Function.update] using hyl
    · right; right; left
      rw [hSW]
      apply Subtype.ext
      funext l
      have hyl := congrFun hy l
      fin_cases l <;>
        simpa [fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
          shift, Function.update] using hyl
    · right; left
      rw [hNW]
      apply Subtype.ext
      funext l
      have hyl := congrFun hy l
      fin_cases l <;>
        simpa [fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
          shift, Function.update] using hyl
    · right; right; right
      rw [hSE]
      apply Subtype.ext
      funext l
      have hyl := congrFun hy l
      fin_cases l <;>
        simpa [fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
          shift, Function.update] using hyl
  · rintro (rfl | rfl | rfl | rfl)
    · rw [hNE]
      exact fkIsingSquare_adj_neighbor n c .east heast
    · rw [hNW]
      exact fkIsingSquare_adj_neighbor n c .north hnorth
    · rw [hSW]
      exact fkIsingSquare_adj_neighbor n c .west hwest
    · rw [hSE]
      exact fkIsingSquare_adj_neighbor n c .south hsouth


end
end StatMech.Universality

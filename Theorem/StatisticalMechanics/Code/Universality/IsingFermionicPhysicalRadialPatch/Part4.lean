/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialRectangle.Part6
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDirichletLimit.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialPatch.Part4


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open Filter Set Topology

noncomputable section

theorem fkIsingSquareRadialPatch_bondMate_right
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (i j : Nat) (hi : i + 1 < m) (hj : j < m) :
    fkIsingSquareBondMate n hn
        (fkIsingSquareRadialPatchEdge n m hm ⟨i, by omega⟩ ⟨j, hj⟩,
          fkIsingSquareRadialPatchRightSide i j) =
      (fkIsingSquareRadialPatchEdge n m hm ⟨i + 1, hi⟩ ⟨j, hj⟩,
        fkIsingSquareRadialPatchLeftSide (i + 1) j) := by
  let a : Fin m := ⟨i, by omega⟩
  let b : Fin m := ⟨i + 1, hi⟩
  let c : Fin m := ⟨j, hj⟩
  change fkIsingSquareBondMate n hn
      (fkIsingSquareRadialPatchEdge n m hm a c,
        fkIsingSquareRadialPatchRightSide i j) =
    (fkIsingSquareRadialPatchEdge n m hm b c,
      fkIsingSquareRadialPatchLeftSide (i + 1) j)
  have hq : fkIsingSquareRadialPatchHalf i j < n := by
    simpa [a, c] using fkIsingSquareRadialPatchHalf_lt hm a c
  have hq' : fkIsingSquareRadialPatchHalf (i + 1) j < n := by
    simpa [b, c] using fkIsingSquareRadialPatchHalf_lt hm b c
  have hx : (fkIsingSquareRadialPatchHalf i j : Int) < (n : Int) := by
    exact_mod_cast hq
  have hxlow : -(n : Int) < (fkIsingSquareRadialPatchHalf i j : Int) := by
    omega
  have hy : (i : Int) - fkIsingSquareRadialPatchHalf i j < (n : Int) := by
    have hin : i < n := by omega
    omega
  have hylow : -(n : Int) <
      (i : Int) - fkIsingSquareRadialPatchHalf i j := by omega
  have hx' : (fkIsingSquareRadialPatchHalf (i + 1) j : Int) < (n : Int) := by
    exact_mod_cast hq'
  have hxlow' : -(n : Int) <
      (fkIsingSquareRadialPatchHalf (i + 1) j : Int) := by omega
  have hy' : (i + 1 : Int) - fkIsingSquareRadialPatchHalf (i + 1) j <
      (n : Int) := by
    have hin : i + 1 < n := by omega
    omega
  have hylow' : -(n : Int) <
      (i + 1 : Int) - fkIsingSquareRadialPatchHalf (i + 1) j := by omega
  by_cases heven : Even (i + j)
  · have hnext : ¬ Even (i + 1 + j) := by
      rw [Nat.not_even_iff]
      have hmod := Nat.even_iff.mp heven
      omega
    have hcoord : 2 * fkIsingSquareRadialPatchHalf i j = i + j := by
      have hmod := Nat.even_iff.mp heven
      unfold fkIsingSquareRadialPatchHalf
      omega
    have hhalf : fkIsingSquareRadialPatchHalf (i + 1) j =
        fkIsingSquareRadialPatchHalf i j + 1 := by
      have hmod := Nat.even_iff.mp heven
      unfold fkIsingSquareRadialPatchHalf
      omega
    have hcoord' : 2 * fkIsingSquareRadialPatchHalf (i + 1) j =
        i + j + 2 := by omega
    rw [fkIsingSquareRadialPatchEdge_eq_east n m hm a c
        (by simpa [a, c] using heven),
      fkIsingSquareRadialPatchEdge_eq_north n m hm b c
        (by simpa [b, c, Nat.add_assoc] using hnext)]
    rw [show fkIsingSquareRadialPatchRightSide i j = .north by
      simp [fkIsingSquareRadialPatchRightSide, heven]]
    rw [show fkIsingSquareRadialPatchLeftSide (i + 1) j = .west by
      simp [fkIsingSquareRadialPatchLeftSide, hnext]]
    apply fkIsingSquareDart_key_injective n
    simp [fkIsingSquareBondMate, fkIsingSquareRadialPatchRightSide,
      heven, fkIsingSquareNextDirection,
      fkIsingSquarePreviousDirection, fkIsingSquareDirectionAvailable,
      fkIsingSquareRadialPatchVertex, a, b, c,
      fkIsingSquareDirectionDart, fkIsingSquareSideCorner,
      fkIsingSquareCornerSide,
      fkIsingSquareEndpointForDirection, fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite, hhalf,
      hx, hxlow, hy, hylow, hx', hxlow', hy', hylow']
  · have hnext : Even (i + 1 + j) := by
      rw [Nat.even_iff]
      have hmod := Nat.not_even_iff.mp heven
      omega
    have hcoord : 2 * fkIsingSquareRadialPatchHalf i j = i + j + 1 := by
      have hmod := Nat.not_even_iff.mp heven
      unfold fkIsingSquareRadialPatchHalf
      omega
    have hhalf : fkIsingSquareRadialPatchHalf (i + 1) j =
        fkIsingSquareRadialPatchHalf i j := by
      have hmod := Nat.not_even_iff.mp heven
      unfold fkIsingSquareRadialPatchHalf
      omega
    have hcoord' : 2 * fkIsingSquareRadialPatchHalf (i + 1) j =
        i + j + 1 := by omega
    rw [fkIsingSquareRadialPatchEdge_eq_north n m hm a c
        (by simpa [a, c] using heven),
      fkIsingSquareRadialPatchEdge_eq_east n m hm b c
        (by simpa [b, c, Nat.add_assoc] using hnext)]
    rw [show fkIsingSquareRadialPatchRightSide i j = .east by
      simp [fkIsingSquareRadialPatchRightSide, heven]]
    rw [show fkIsingSquareRadialPatchLeftSide (i + 1) j = .south by
      simp [fkIsingSquareRadialPatchLeftSide, hnext]]
    apply fkIsingSquareDart_key_injective n
    simp [fkIsingSquareBondMate, fkIsingSquareRadialPatchRightSide,
      heven, fkIsingSquareNextDirection,
      fkIsingSquarePreviousDirection, fkIsingSquareDirectionAvailable,
      fkIsingSquareRadialPatchVertex, a, b, c,
      fkIsingSquareDirectionDart, fkIsingSquareSideCorner,
      fkIsingSquareCornerSide,
      fkIsingSquareEndpointForDirection, fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite, hhalf,
      hx, hxlow, hy, hylow, hx', hxlow', hy', hylow']
    apply Subtype.ext
    funext k
    fin_cases k <;> simp <;> ring


end
end StatMech.Universality

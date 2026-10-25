/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredFourSectorAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCenteredNESectorRate
import Structure.StatisticalMechanics.Code.Universality.IsingFermionicCenteredFourSectorAssembly


namespace StatMech.Universality

noncomputable section

theorem FKIsingExpandingCenteredTopRightBoundaryEdgeBounds.outerCollarBound
    {L : NNReal} {k : Nat}
    (h : FKIsingExpandingCenteredTopRightBoundaryEdgeBounds L k) :
    FKIsingExpandingCenteredOuterCollarBound L k := by
  constructor
  · intro a b ha hb houter
    by_cases hright : a + 2 = 2 * fkIsingExpandingSquareSide k
    · exact h.horizontalRight a b ha hb hright
    · have htop : b + 1 = 2 * fkIsingExpandingSquareSide k := by omega
      exact h.horizontalTop a b ha hb htop
  · intro a b ha hb houter
    by_cases hright : a + 1 = 2 * fkIsingExpandingSquareSide k
    · exact h.verticalRight a b ha hb hright
    · have htop : b + 2 = 2 * fkIsingExpandingSquareSide k := by omega
      exact h.verticalTop a b ha hb htop


theorem
    fkIsingExpandingCenteredTopRightBoundaryEdgeBounds_of_diagonal
    (L : NNReal) (k : Nat)
    (hright : ∀ J,
      FKIsingExpandingCenteredRightDiagonalCellBound L k J)
    (htop : ∀ I,
      FKIsingExpandingCenteredTopDiagonalCellBound L k I) :
    FKIsingExpandingCenteredTopRightBoundaryEdgeBounds L k := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply fkIsingExpandingCenteredHorizontalRight_of_even_diagonal L k
    intro J hJ0 hJ _heven
    exact hright J hJ0 hJ
  · exact fkIsingExpandingCenteredHorizontalTop_of_diagonal L k htop
  · exact fkIsingExpandingCenteredVerticalRight_of_diagonal L k hright
  · apply fkIsingExpandingCenteredVerticalTop_of_even_diagonal L k
    intro I hI0 hI _heven
    exact htop I hI0 hI


theorem fkIsingExpandingCenteredOuterCollarBound_of_diagonal
    (L : NNReal) (k : Nat)
    (hright : ∀ J,
      FKIsingExpandingCenteredRightDiagonalCellBound L k J)
    (htop : ∀ I,
      FKIsingExpandingCenteredTopDiagonalCellBound L k I) :
    FKIsingExpandingCenteredOuterCollarBound L k :=
  (fkIsingExpandingCenteredTopRightBoundaryEdgeBounds_of_diagonal
    L k hright htop).outerCollarBound


theorem
    fkIsingExpandingCenteredNeighborTransport_of_four_sector_diagonal_and_collar
    (L : NNReal) (N : Nat) (hN : 1 ≤ N)
    (hdiag : ∀ q : Fin 4, ∀ k, N ≤ k → ∀ i j,
      isingCenteredRadialIndexSector
          (fkIsingExpandingSquareSide k) i j = q →
        FKIsingExpandingCenteredDiagonalCellBound L k i j)
    (hcollar : ∀ k, N ≤ k →
      FKIsingExpandingCenteredOuterCollarBound L k) :
    FKIsingExpandingCenteredNeighborTransport := by
  apply fkIsingExpandingCenteredNeighborTransport_of_four_sector_bounds
    (2 * L) N
  · intro q k hk a b _hsector
    intro ha hb
    by_cases hinner :
        a + 2 < 2 * fkIsingExpandingSquareSide k ∧
          b + 1 < 2 * fkIsingExpandingSquareSide k
    · let i := a + 1
      let j := if b = 0 then 1 else b
      have hk1 : 1 ≤ k := le_trans hN hk
      have hn4 : 4 ≤ fkIsingExpandingSquareSide k := by
        rw [fkIsingExpandingSquareSide]
        nlinarith
      have hi0 : 0 < i := by simp [i]
      have hi1 : i + 1 < 2 * fkIsingExpandingSquareSide k := by
        simpa [i] using hinner.1
      have hj0 : 0 < j := by
        simp only [j]
        split <;> omega
      have hj1 : j + 1 < 2 * fkIsingExpandingSquareSide k := by
        simp only [j]
        split
        · omega
        · exact hinner.2
      have hd := hdiag
        (isingCenteredRadialIndexSector
          (fkIsingExpandingSquareSide k) i j) k hk i j rfl
          hi0 hi1 hj0 hj1
      dsimp only [FKIsingExpandingCenteredDiagonalCellBound] at hd
      have hedges :=
        fkIsingSquareBoundaryCenteredRadialPatchFullObservable_cell_edges_le
          (fkIsingExpandingSquareSide k) i j
          (fkIsingExpandingSquareSide_pos k) hi0 hi1 hj0 hj1
          (Real.sqrt (2 * fkIsingExpandingSquareMesh k))
          (fkIsingExpandingSquareScale k * (L : Real)) hd.1 hd.2
      dsimp only at hedges
      by_cases hb0 : b = 0
      · subst b
        rw [norm_sub_rev]
        convert hedges.2.2.2 using 1 <;> simp [i, j] <;> ring
      · convert hedges.2.1 using 1 <;> simp [i, j, hb0] <;> ring
    · exact (hcollar k hk).1 a b ha hb hinner ha hb
  · intro q k hk a b _hsector
    intro ha hb
    by_cases hinner :
        a + 1 < 2 * fkIsingExpandingSquareSide k ∧
          b + 2 < 2 * fkIsingExpandingSquareSide k
    · let i := if a = 0 then 1 else a
      let j := b + 1
      have hk1 : 1 ≤ k := le_trans hN hk
      have hn4 : 4 ≤ fkIsingExpandingSquareSide k := by
        rw [fkIsingExpandingSquareSide]
        nlinarith
      have hi0 : 0 < i := by
        simp only [i]
        split <;> omega
      have hi1 : i + 1 < 2 * fkIsingExpandingSquareSide k := by
        simp only [i]
        split
        · omega
        · exact hinner.1
      have hj0 : 0 < j := by simp [j]
      have hj1 : j + 1 < 2 * fkIsingExpandingSquareSide k := by
        simpa [j] using hinner.2
      have hd := hdiag
        (isingCenteredRadialIndexSector
          (fkIsingExpandingSquareSide k) i j) k hk i j rfl
          hi0 hi1 hj0 hj1
      dsimp only [FKIsingExpandingCenteredDiagonalCellBound] at hd
      have hedges :=
        fkIsingSquareBoundaryCenteredRadialPatchFullObservable_cell_edges_le
          (fkIsingExpandingSquareSide k) i j
          (fkIsingExpandingSquareSide_pos k) hi0 hi1 hj0 hj1
          (Real.sqrt (2 * fkIsingExpandingSquareMesh k))
          (fkIsingExpandingSquareScale k * (L : Real)) hd.1 hd.2
      dsimp only at hedges
      by_cases ha0 : a = 0
      · subst a
        convert hedges.2.2.1 using 1 <;> simp [i, j] <;> ring
      · rw [norm_sub_rev]
        convert hedges.1 using 1 <;> simp [i, j, ha0] <;> ring
    · exact (hcollar k hk).2 a b ha hb hinner ha hb


theorem
    fkIsingExpandingCenteredStrictNeighborTransport_of_four_sector_diagonal
    (L : NNReal) (N : Nat) (hN : 1 ≤ N)
    (hdiag : ∀ q : Fin 4, ∀ k, N ≤ k → ∀ i j,
      isingCenteredRadialIndexSector
          (fkIsingExpandingSquareSide k) i j = q →
        FKIsingExpandingCenteredDiagonalCellBound L k i j) :
    FKIsingExpandingCenteredStrictNeighborTransport := by
  refine ⟨2 * L, N, ?_⟩
  intro k hk
  constructor
  · intro a b ha hb ha2 hb1
    let i := a + 1
    let j := if b = 0 then 1 else b
    have hk1 : 1 ≤ k := le_trans hN hk
    have hn4 : 4 ≤ fkIsingExpandingSquareSide k := by
      rw [fkIsingExpandingSquareSide]
      nlinarith
    have hi0 : 0 < i := by simp [i]
    have hi1 : i + 1 < 2 * fkIsingExpandingSquareSide k := by
      simpa [i] using ha2
    have hj0 : 0 < j := by
      simp only [j]
      split <;> omega
    have hj1 : j + 1 < 2 * fkIsingExpandingSquareSide k := by
      simp only [j]
      split
      · omega
      · exact hb1
    have hd := hdiag
      (isingCenteredRadialIndexSector
        (fkIsingExpandingSquareSide k) i j) k hk i j rfl
        hi0 hi1 hj0 hj1
    dsimp only [FKIsingExpandingCenteredDiagonalCellBound] at hd
    have hedges :=
      fkIsingSquareBoundaryCenteredRadialPatchFullObservable_cell_edges_le
        (fkIsingExpandingSquareSide k) i j
        (fkIsingExpandingSquareSide_pos k) hi0 hi1 hj0 hj1
        (Real.sqrt (2 * fkIsingExpandingSquareMesh k))
        (fkIsingExpandingSquareScale k * (L : Real)) hd.1 hd.2
    dsimp only at hedges
    by_cases hb0 : b = 0
    · subst b
      rw [norm_sub_rev]
      convert hedges.2.2.2 using 1 <;> simp [i, j] <;> ring
    · convert hedges.2.1 using 1 <;> simp [i, j, hb0] <;> ring
  · intro a b ha hb ha1 hb2
    let i := if a = 0 then 1 else a
    let j := b + 1
    have hk1 : 1 ≤ k := le_trans hN hk
    have hn4 : 4 ≤ fkIsingExpandingSquareSide k := by
      rw [fkIsingExpandingSquareSide]
      nlinarith
    have hi0 : 0 < i := by
      simp only [i]
      split <;> omega
    have hi1 : i + 1 < 2 * fkIsingExpandingSquareSide k := by
      simp only [i]
      split
      · omega
      · exact ha1
    have hj0 : 0 < j := by simp [j]
    have hj1 : j + 1 < 2 * fkIsingExpandingSquareSide k := by
      simpa [j] using hb2
    have hd := hdiag
      (isingCenteredRadialIndexSector
        (fkIsingExpandingSquareSide k) i j) k hk i j rfl
        hi0 hi1 hj0 hj1
    dsimp only [FKIsingExpandingCenteredDiagonalCellBound] at hd
    have hedges :=
      fkIsingSquareBoundaryCenteredRadialPatchFullObservable_cell_edges_le
        (fkIsingExpandingSquareSide k) i j
        (fkIsingExpandingSquareSide_pos k) hi0 hi1 hj0 hj1
        (Real.sqrt (2 * fkIsingExpandingSquareMesh k))
        (fkIsingExpandingSquareScale k * (L : Real)) hd.1 hd.2
    dsimp only at hedges
    by_cases ha0 : a = 0
    · subst a
      convert hedges.2.2.1 using 1 <;> simp [i, j] <;> ring
    · rw [norm_sub_rev]
      convert hedges.1 using 1 <;> simp [i, j, ha0] <;> ring


theorem
    fkIsingExpandingCenteredNeighborTransport_of_four_sector_and_boundary_diagonal
    (L : NNReal) (N : Nat) (hN : 1 ≤ N)
    (hdiag : ∀ q : Fin 4, ∀ k, N ≤ k → ∀ i j,
      isingCenteredRadialIndexSector
          (fkIsingExpandingSquareSide k) i j = q →
        FKIsingExpandingCenteredDiagonalCellBound L k i j)
    (hright : ∀ k, N ≤ k → ∀ J,
      FKIsingExpandingCenteredRightDiagonalCellBound L k J)
    (htop : ∀ k, N ≤ k → ∀ I,
      FKIsingExpandingCenteredTopDiagonalCellBound L k I) :
    FKIsingExpandingCenteredNeighborTransport := by
  apply
    fkIsingExpandingCenteredNeighborTransport_of_four_sector_diagonal_and_collar
      L N hN hdiag
  intro k hk
  exact fkIsingExpandingCenteredOuterCollarBound_of_diagonal
    L k (hright k hk) (htop k hk)

end
end StatMech.Universality

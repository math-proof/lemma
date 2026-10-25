/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredFourSectorAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCenteredNESectorRate
import Def.StatisticalMechanics.Code.Universality.IsingFermionicCenteredFourSectorAssembly.Part2


namespace StatMech.Universality

noncomputable section

theorem
    fkIsingExpandingCenteredVerticalTop_of_even_diagonal
    (L : NNReal) (k : Nat)
    (hdiag : ∀ I,
      FKIsingExpandingCenteredTopEvenDiagonalCellBound L k I) :
    ∀ a b : Nat,
      ∀ (ha : a < 2 * fkIsingExpandingSquareSide k)
        (hb : b + 1 < 2 * fkIsingExpandingSquareSide k),
        b + 2 = 2 * fkIsingExpandingSquareSide k →
          FKIsingExpandingCenteredVerticalNeighborBound (2 * L) k a b := by
  intro a b ha hb htop
  intro _ha _hb
  let n := fkIsingExpandingSquareSide k
  let F := fkIsingSquareBoundaryCenteredRadialPatchFullObservable n
    (fkIsingExpandingSquareSide_pos k)
  let normalization := Real.sqrt (2 * fkIsingExpandingSquareMesh k)
  let delta := fkIsingExpandingSquareScale k * (L : Real)
  have hn : 0 < n := fkIsingExpandingSquareSide_pos k
  have hb0 : b = 2 * n - 2 := by omega
  subst b
  by_cases haEven : Even a
  · let I := a + 1
    have hI0 : 0 < I := by simp [I]
    have hI : I < 2 * n := by
      have hmod := Nat.even_iff.mp haEven
      dsimp only [I, n]
      omega
    have heven : Even (I + (2 * n - 1)) := by
      rw [Nat.even_iff]
      have hmod := Nat.even_iff.mp haEven
      dsimp only [I]
      omega
    have hd := hdiag I hI0 (by simpa [n] using hI) (by simpa [n] using heven)
    dsimp only [FKIsingExpandingCenteredTopEvenDiagonalCellBound] at hd
    have hquad :=
      fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_top_of_even
        n I hn hI0 hI heven
    have hcycle := IsingSquareSHolomorphicQuad.projection_cycle _ _ _ _ hquad
    have hedges := projectionCycle_crossParity_norm_div_sub_div_le
      _ _ _ _ normalization delta
      hcycle.1 hcycle.2.1 hcycle.2.2.1 hcycle.2.2.2 hd.1 hd.2
    convert hedges.2.2.1 using 1 <;>
      simp [FKIsingExpandingCenteredVerticalNeighborBound, F,
        normalization, delta, I, n] <;> try ring <;> omega
  · let I := a
    have hI0 : 0 < I := by
      dsimp only [I]
      have hodd := Nat.not_even_iff.mp haEven
      omega
    have hI : I < 2 * n := by simpa [I, n] using ha
    have heven : Even (I + (2 * n - 1)) := by
      rw [Nat.even_iff]
      have hmod := Nat.not_even_iff.mp haEven
      dsimp only [I]
      omega
    have hd := hdiag I hI0 (by simpa [n] using hI) (by simpa [n] using heven)
    dsimp only [FKIsingExpandingCenteredTopEvenDiagonalCellBound] at hd
    have hquad :=
      fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_top_of_even
        n I hn hI0 hI heven
    have hcycle := IsingSquareSHolomorphicQuad.projection_cycle _ _ _ _ hquad
    have hedges := projectionCycle_crossParity_norm_div_sub_div_le
      _ _ _ _ normalization delta
      hcycle.1 hcycle.2.1 hcycle.2.2.1 hcycle.2.2.2 hd.1 hd.2
    rw [norm_sub_rev]
    convert hedges.1 using 1 <;>
      simp [FKIsingExpandingCenteredVerticalNeighborBound, F,
        normalization, delta, I, n] <;> try ring <;> omega


end
end StatMech.Universality

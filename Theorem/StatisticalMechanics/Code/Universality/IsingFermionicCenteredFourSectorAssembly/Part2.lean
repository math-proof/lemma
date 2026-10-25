/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredFourSectorAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCenteredNESectorRate
import Def.StatisticalMechanics.Code.Universality.IsingFermionicCenteredFourSectorAssembly


namespace StatMech.Universality

noncomputable section

theorem
    fkIsingExpandingCenteredHorizontalRight_of_even_diagonal
    (L : NNReal) (k : Nat)
    (hdiag : ∀ J,
      FKIsingExpandingCenteredRightEvenDiagonalCellBound L k J) :
    ∀ a b : Nat,
      ∀ (ha : a + 1 < 2 * fkIsingExpandingSquareSide k)
        (hb : b < 2 * fkIsingExpandingSquareSide k),
        a + 2 = 2 * fkIsingExpandingSquareSide k →
          FKIsingExpandingCenteredHorizontalNeighborBound (2 * L) k a b := by
  intro a b ha hb hright
  intro _ha _hb
  let n := fkIsingExpandingSquareSide k
  let F := fkIsingSquareBoundaryCenteredRadialPatchFullObservable n
    (fkIsingExpandingSquareSide_pos k)
  let normalization := Real.sqrt (2 * fkIsingExpandingSquareMesh k)
  let delta := fkIsingExpandingSquareScale k * (L : Real)
  have hn : 0 < n := fkIsingExpandingSquareSide_pos k
  have ha0 : a = 2 * n - 2 := by omega
  subst a
  by_cases hbEven : Even b
  · let J := b + 1
    have hJ0 : 0 < J := by simp [J]
    have hJ : J < 2 * n := by
      have hmod := Nat.even_iff.mp hbEven
      dsimp only [J, n]
      omega
    have heven : Even ((2 * n - 1) + J) := by
      rw [Nat.even_iff]
      have hmod := Nat.even_iff.mp hbEven
      dsimp only [J]
      omega
    have hd := hdiag J hJ0 (by simpa [n] using hJ) (by simpa [n] using heven)
    dsimp only [FKIsingExpandingCenteredRightEvenDiagonalCellBound] at hd
    have hquad :=
      fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_right_of_even
        n J hn hJ0 hJ heven
    have hcycle := IsingSquareSHolomorphicQuad.projection_cycle _ _ _ _ hquad
    have hedges := projectionCycle_crossParity_norm_div_sub_div_le
      _ _ _ _ normalization delta
      hcycle.1 hcycle.2.1 hcycle.2.2.1 hcycle.2.2.2 hd.1 hd.2
    rw [norm_sub_rev]
    convert hedges.2.2.2 using 1 <;>
      simp [FKIsingExpandingCenteredHorizontalNeighborBound, F,
        normalization, delta, J, n] <;> try ring <;> omega
  · let J := b
    have hJ0 : 0 < J := by
      dsimp only [J]
      have hodd := Nat.not_even_iff.mp hbEven
      omega
    have hJ : J < 2 * n := by simpa [J, n] using hb
    have heven : Even ((2 * n - 1) + J) := by
      rw [Nat.even_iff]
      have hmod := Nat.not_even_iff.mp hbEven
      dsimp only [J]
      omega
    have hd := hdiag J hJ0 (by simpa [n] using hJ) (by simpa [n] using heven)
    dsimp only [FKIsingExpandingCenteredRightEvenDiagonalCellBound] at hd
    have hquad :=
      fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_right_of_even
        n J hn hJ0 hJ heven
    have hcycle := IsingSquareSHolomorphicQuad.projection_cycle _ _ _ _ hquad
    have hedges := projectionCycle_crossParity_norm_div_sub_div_le
      _ _ _ _ normalization delta
      hcycle.1 hcycle.2.1 hcycle.2.2.1 hcycle.2.2.2 hd.1 hd.2
    convert hedges.2.1 using 1 <;>
      simp [FKIsingExpandingCenteredHorizontalNeighborBound, F,
        normalization, delta, J, n] <;> try ring <;> omega


end
end StatMech.Universality

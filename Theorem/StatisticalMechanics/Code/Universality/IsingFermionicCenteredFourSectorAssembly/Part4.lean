/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredFourSectorAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCenteredNESectorRate
import Def.StatisticalMechanics.Code.Universality.IsingFermionicCenteredFourSectorAssembly.Part3


namespace StatMech.Universality

noncomputable section

theorem fkIsingExpandingCenteredHorizontalTop_of_diagonal
    (L : NNReal) (k : Nat)
    (hdiag : ∀ I, FKIsingExpandingCenteredTopDiagonalCellBound L k I) :
    ∀ a b : Nat,
      ∀ (ha : a + 1 < 2 * fkIsingExpandingSquareSide k)
        (hb : b < 2 * fkIsingExpandingSquareSide k),
        b + 1 = 2 * fkIsingExpandingSquareSide k →
          FKIsingExpandingCenteredHorizontalNeighborBound (2 * L) k a b := by
  intro a b ha hb htop
  intro _ha _hb
  let n := fkIsingExpandingSquareSide k
  let I := a + 1
  let F := fkIsingSquareBoundaryCenteredRadialPatchFullObservable n
    (fkIsingExpandingSquareSide_pos k)
  let normalization := Real.sqrt (2 * fkIsingExpandingSquareMesh k)
  let delta := fkIsingExpandingSquareScale k * (L : Real)
  have hn : 0 < n := fkIsingExpandingSquareSide_pos k
  have hI0 : 0 < I := by simp [I]
  have hI : I < 2 * n := by simpa [I, n] using ha
  have hb0 : b = 2 * n - 1 := by omega
  subst b
  have hd := hdiag I hI0 (by simpa [n] using hI)
  dsimp only [FKIsingExpandingCenteredTopDiagonalCellBound] at hd
  by_cases heven : Even (I + (2 * n - 1))
  · have hquad :=
      fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_top_of_even
        n I hn hI0 hI heven
    have hcycle := IsingSquareSHolomorphicQuad.projection_cycle _ _ _ _ hquad
    have hedges := projectionCycle_crossParity_norm_div_sub_div_le
      _ _ _ _ normalization delta
      hcycle.1 hcycle.2.1 hcycle.2.2.1 hcycle.2.2.2 hd.1 hd.2
    convert hedges.2.1 using 1 <;>
      simp [FKIsingExpandingCenteredHorizontalNeighborBound, F,
        normalization, delta, I, n] <;> try ring <;> omega
  · have hquad :=
      fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_top_of_odd
        n I hn hI0 hI heven
    have hcycle := IsingSquareSHolomorphicQuad.projection_cycle _ _ _ _ hquad
    have hSN := hd.1
    have hWE := hd.2
    rw [norm_sub_rev] at hSN hWE
    have hodd := projectionCycle_crossParity_norm_div_sub_div_le
      _ _ _ _ normalization delta
      hcycle.1 hcycle.2.1 hcycle.2.2.1 hcycle.2.2.2 hSN hWE
    convert hodd.2.2.2 using 1 <;>
      simp [FKIsingExpandingCenteredHorizontalNeighborBound, F,
        normalization, delta, I, n] <;> try ring <;> omega


theorem fkIsingExpandingCenteredVerticalRight_of_diagonal
    (L : NNReal) (k : Nat)
    (hdiag : ∀ J, FKIsingExpandingCenteredRightDiagonalCellBound L k J) :
    ∀ a b : Nat,
      ∀ (ha : a < 2 * fkIsingExpandingSquareSide k)
        (hb : b + 1 < 2 * fkIsingExpandingSquareSide k),
        a + 1 = 2 * fkIsingExpandingSquareSide k →
          FKIsingExpandingCenteredVerticalNeighborBound (2 * L) k a b := by
  intro a b ha hb hright
  intro _ha _hb
  let n := fkIsingExpandingSquareSide k
  let J := b + 1
  let F := fkIsingSquareBoundaryCenteredRadialPatchFullObservable n
    (fkIsingExpandingSquareSide_pos k)
  let normalization := Real.sqrt (2 * fkIsingExpandingSquareMesh k)
  let delta := fkIsingExpandingSquareScale k * (L : Real)
  have hn : 0 < n := fkIsingExpandingSquareSide_pos k
  have hJ0 : 0 < J := by simp [J]
  have hJ : J < 2 * n := by simpa [J, n] using hb
  have ha0 : a = 2 * n - 1 := by omega
  subst a
  have hd := hdiag J hJ0 (by simpa [n] using hJ)
  dsimp only [FKIsingExpandingCenteredRightDiagonalCellBound] at hd
  by_cases heven : Even ((2 * n - 1) + J)
  · have hquad :=
      fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_right_of_even
        n J hn hJ0 hJ heven
    have hcycle := IsingSquareSHolomorphicQuad.projection_cycle _ _ _ _ hquad
    have hedges := projectionCycle_crossParity_norm_div_sub_div_le
      _ _ _ _ normalization delta
      hcycle.1 hcycle.2.1 hcycle.2.2.1 hcycle.2.2.2 hd.1 hd.2
    rw [norm_sub_rev]
    convert hedges.1 using 1 <;>
      simp [FKIsingExpandingCenteredVerticalNeighborBound, F,
        normalization, delta, J, n] <;> try ring <;> omega
  · have hquad :=
      fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_right_of_odd
        n J hn hJ0 hJ heven
    have hcycle := IsingSquareSHolomorphicQuad.projection_cycle _ _ _ _ hquad
    have hSN := hd.1
    have hWE := hd.2
    rw [norm_sub_rev] at hSN hWE
    have hodd := projectionCycle_crossParity_norm_div_sub_div_le
      _ _ _ _ normalization delta
      hcycle.1 hcycle.2.1 hcycle.2.2.1 hcycle.2.2.2 hSN hWE
    rw [norm_sub_rev]
    convert hodd.2.2.1 using 1 <;>
      simp [FKIsingExpandingCenteredVerticalNeighborBound, F,
        normalization, delta, J, n] <;> try ring <;> omega


theorem
    fkIsingExpandingBoundarySquareCenteredNE_diagonalCellBound
    (k baseI baseJ R rho cutoff a b : Nat) (hk : 1 ≤ k)
    (hfitI : baseI + R + 1 < fkIsingExpandingSquareSide k)
    (hfitJ : baseJ + R + 1 < fkIsingExpandingSquareSide k)
    (hcutoff : 0 < cutoff)
    (hdeep : ∀ q : IsingLeapfrogBox R,
      fkIsingSquareRadialPatchWindowCell
          (fkIsingExpandingSquareSide k) baseI baseJ R hfitI hfitJ q ∈
        fkIsingSquareRadialPatchDeepCells
          (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide k)
          (le_refl _) (by
            simp only [fkIsingExpandingSquareSide, pow_two]
            nlinarith) cutoff)
    (hsideCutoff : fkIsingExpandingSquareSide k ≤ 4 * cutoff)
    (hsideRho : fkIsingExpandingSquareSide k ≤ 4 * rho)
    (ha0 : 0 < a) (haR : a < R) (hb0 : 0 < b) (hbR : b < R)
    (hrho : 0 < rho)
    (hmarginN : IsingLeapfrogInteriorMargin R rho
      (⟨a, by omega⟩, ⟨b - 1, by omega⟩))
    (hmarginE : IsingLeapfrogInteriorMargin R rho
      (⟨a, by omega⟩, ⟨b, by omega⟩))
    (hmarginS : IsingLeapfrogInteriorMargin R rho
      (⟨a - 1, by omega⟩, ⟨b, by omega⟩))
    (hmarginW : IsingLeapfrogInteriorMargin R rho
      (⟨a - 1, by omega⟩, ⟨b - 1, by omega⟩)) :
    FKIsingExpandingCenteredDiagonalCellBound 40000 k
      (fkIsingExpandingSquareSide k + (baseI + a))
      (fkIsingExpandingSquareSide k + (baseJ + b)) := by
  intro hi0 hi1 hj0 hj1
  let pN : IsingLeapfrogBox R :=
    (⟨a, by omega⟩, ⟨b - 1, by omega⟩)
  let pE : IsingLeapfrogBox R :=
    (⟨a, by omega⟩, ⟨b, by omega⟩)
  let pS : IsingLeapfrogBox R :=
    (⟨a - 1, by omega⟩, ⟨b, by omega⟩)
  let pW : IsingLeapfrogBox R :=
    (⟨a - 1, by omega⟩, ⟨b - 1, by omega⟩)
  have hNS :=
    fkIsingExpandingBoundarySquareCenteredNE_normalizedNeighbor_norm_sub_le
      k baseI baseJ R rho cutoff hk hfitI hfitJ hcutoff hdeep
      hsideCutoff hsideRho pN pS hrho
      (by simpa [pN] using hmarginN) (by simpa [pS] using hmarginS) (by
        unfold IsingLeapfrogDiagonalAdjacent
        simp [pN, pS, Nat.dist]
        omega)
  have hEW :=
    fkIsingExpandingBoundarySquareCenteredNE_normalizedNeighbor_norm_sub_le
      k baseI baseJ R rho cutoff hk hfitI hfitJ hcutoff hdeep
      hsideCutoff hsideRho pE pW hrho
      (by simpa [pE] using hmarginE) (by simpa [pW] using hmarginW) (by
        unfold IsingLeapfrogDiagonalAdjacent
        simp [pE, pW, Nat.dist]
        omega)
  have hIa : fkIsingExpandingSquareSide k + (baseI + (a - 1)) =
      fkIsingExpandingSquareSide k + (baseI + a) - 1 := by omega
  have hJb : fkIsingExpandingSquareSide k + (baseJ + (b - 1)) =
      fkIsingExpandingSquareSide k + (baseJ + b) - 1 := by omega
  constructor
  · simpa [pN, pS, hIa, hJb] using hNS
  · simpa [pE, pW, hIa, hJb] using hEW


end
end StatMech.Universality

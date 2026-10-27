import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCenteredFourSectorAssembly.Part5
open StatMech StatMech.Universality


/--
[fkIsingSquareBoundaryCenteredRadialPatchFullObservable_cell_edges_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredFourSectorAssembly.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryCenteredRadialPatchFullObservable_cell_edges_le_eq
  {n i j : Nat}
  {r delta : Real}
-- given
  (hn : 0 < n)
  (hi0 : 0 < i)
  (hi1 : i + 1 < 2 * n)
  (hj0 : 0 < j)
  (hj1 : j + 1 < 2 * n)
  (hNS : ‖fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨i, by omega⟩ ⟨j - 1, by omega⟩ / (r : Complex) - fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨i - 1, by omega⟩ ⟨j, by omega⟩ / (r : Complex)‖ ≤ delta)
  (hEW : ‖fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨i, by omega⟩ ⟨j, by omega⟩ / (r : Complex) - fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ / (r : Complex)‖ ≤ delta) :
-- imply
  let north := fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨i, by omega⟩ ⟨j - 1, by omega⟩ let east := fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨i, by omega⟩ ⟨j, by omega⟩ let south := fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨i - 1, by omega⟩ ⟨j, by omega⟩ let west := fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ ‖north / (r : Complex) - east / (r : Complex)‖ ≤ 2 * delta ∧ ‖east / (r : Complex) - south / (r : Complex)‖ ≤ 2 * delta ∧ ‖south / (r : Complex) - west / (r : Complex)‖ ≤ 2 * delta ∧ ‖west / (r : Complex) - north / (r : Complex)‖ ≤ 2 * delta := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryCenteredRadialPatchFullObservable_cell_edges_le n i j hn hi0 hi1 hj0 hj1 r delta hNS hEW

/--
[fkIsingExpandingCenteredHorizontalRight_of_even_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredFourSectorAssembly.lean)
-/
@[path]
private lemma fkIsingExpandingCenteredHorizontalRight_of_even_diagonal_eq
  {L : NNReal}
  {k : Nat}
-- given
  (hdiag : ∀ J, FKIsingExpandingCenteredRightEvenDiagonalCellBound L k J) :
-- imply
  ∀ a b : Nat, ∀ (ha : a + 1 < 2 * fkIsingExpandingSquareSide k) (hb : b < 2 * fkIsingExpandingSquareSide k), a + 2 = 2 * fkIsingExpandingSquareSide k → FKIsingExpandingCenteredHorizontalNeighborBound (2 * L) k a b := by
-- proof
  apply StatMech.Universality.fkIsingExpandingCenteredHorizontalRight_of_even_diagonal L k hdiag

/--
[fkIsingExpandingCenteredVerticalTop_of_even_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredFourSectorAssembly.lean)
-/
@[path]
private lemma fkIsingExpandingCenteredVerticalTop_of_even_diagonal_eq
  {L : NNReal}
  {k : Nat}
-- given
  (hdiag : ∀ I, FKIsingExpandingCenteredTopEvenDiagonalCellBound L k I) :
-- imply
  ∀ a b : Nat, ∀ (ha : a < 2 * fkIsingExpandingSquareSide k) (hb : b + 1 < 2 * fkIsingExpandingSquareSide k), b + 2 = 2 * fkIsingExpandingSquareSide k → FKIsingExpandingCenteredVerticalNeighborBound (2 * L) k a b := by
-- proof
  apply StatMech.Universality.fkIsingExpandingCenteredVerticalTop_of_even_diagonal L k hdiag

/--
[fkIsingExpandingCenteredHorizontalTop_of_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredFourSectorAssembly.lean)
-/
@[path]
private lemma fkIsingExpandingCenteredHorizontalTop_of_diagonal_eq
  {L : NNReal}
  {k : Nat}
-- given
  (hdiag : ∀ I, FKIsingExpandingCenteredTopDiagonalCellBound L k I) :
-- imply
  ∀ a b : Nat, ∀ (ha : a + 1 < 2 * fkIsingExpandingSquareSide k) (hb : b < 2 * fkIsingExpandingSquareSide k), b + 1 = 2 * fkIsingExpandingSquareSide k → FKIsingExpandingCenteredHorizontalNeighborBound (2 * L) k a b := by
-- proof
  apply StatMech.Universality.fkIsingExpandingCenteredHorizontalTop_of_diagonal L k hdiag

/--
[fkIsingExpandingCenteredVerticalRight_of_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredFourSectorAssembly.lean)
-/
@[path]
private lemma fkIsingExpandingCenteredVerticalRight_of_diagonal_eq
  {L : NNReal}
  {k : Nat}
-- given
  (hdiag : ∀ J, FKIsingExpandingCenteredRightDiagonalCellBound L k J) :
-- imply
  ∀ a b : Nat, ∀ (ha : a < 2 * fkIsingExpandingSquareSide k) (hb : b + 1 < 2 * fkIsingExpandingSquareSide k), a + 1 = 2 * fkIsingExpandingSquareSide k → FKIsingExpandingCenteredVerticalNeighborBound (2 * L) k a b := by
-- proof
  apply StatMech.Universality.fkIsingExpandingCenteredVerticalRight_of_diagonal L k hdiag

/--
[fkIsingExpandingBoundarySquareCenteredNE_diagonalCellBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredFourSectorAssembly.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquareCenteredNE_diagonalCellBound_eq
  {k baseI baseJ R rho cutoff a b : Nat}
-- given
  (hk : 1 ≤ k)
  (hfitI : baseI + R + 1 < fkIsingExpandingSquareSide k)
  (hfitJ : baseJ + R + 1 < fkIsingExpandingSquareSide k)
  (hcutoff : 0 < cutoff)
  (hdeep : ∀ q : IsingLeapfrogBox R, fkIsingSquareRadialPatchWindowCell (fkIsingExpandingSquareSide k) baseI baseJ R hfitI hfitJ q ∈ fkIsingSquareRadialPatchDeepCells (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide k) (le_refl _) (by simp only [fkIsingExpandingSquareSide, pow_two] nlinarith) cutoff)
  (hsideCutoff : fkIsingExpandingSquareSide k ≤ 4 * cutoff)
  (hsideRho : fkIsingExpandingSquareSide k ≤ 4 * rho)
  (ha0 : 0 < a)
  (haR : a < R)
  (hb0 : 0 < b)
  (hbR : b < R)
  (hrho : 0 < rho)
  (hmarginN : IsingLeapfrogInteriorMargin R rho (⟨a, by omega⟩, ⟨b - 1, by omega⟩))
  (hmarginE : IsingLeapfrogInteriorMargin R rho (⟨a, by omega⟩, ⟨b, by omega⟩))
  (hmarginS : IsingLeapfrogInteriorMargin R rho (⟨a - 1, by omega⟩, ⟨b, by omega⟩))
  (hmarginW : IsingLeapfrogInteriorMargin R rho (⟨a - 1, by omega⟩, ⟨b - 1, by omega⟩)) :
-- imply
  FKIsingExpandingCenteredDiagonalCellBound 40000 k (fkIsingExpandingSquareSide k + (baseI + a)) (fkIsingExpandingSquareSide k + (baseJ + b)) := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquareCenteredNE_diagonalCellBound k baseI baseJ R rho cutoff a b hk hfitI hfitJ hcutoff hdeep hsideCutoff hsideRho ha0 haR hb0 hbR hrho hmarginN hmarginE hmarginS hmarginW

/--
[FKIsingExpandingCenteredTopRightBoundaryEdgeBounds.outerCollarBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredFourSectorAssembly.lean)
-/
@[path]
private lemma outerCollarBound_eq
  {L : NNReal}
  {k : Nat}
-- given
  (h : FKIsingExpandingCenteredTopRightBoundaryEdgeBounds L k) :
-- imply
  FKIsingExpandingCenteredOuterCollarBound L k := by
-- proof
  apply StatMech.Universality.FKIsingExpandingCenteredTopRightBoundaryEdgeBounds.outerCollarBound h

/--
[fkIsingExpandingCenteredTopRightBoundaryEdgeBounds_of_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredFourSectorAssembly.lean)
-/
@[path]
private lemma fkIsingExpandingCenteredTopRightBoundaryEdgeBounds_of_diagonal_eq
  {L : NNReal}
  {k : Nat}
-- given
  (hright : ∀ J, FKIsingExpandingCenteredRightDiagonalCellBound L k J)
  (htop : ∀ I, FKIsingExpandingCenteredTopDiagonalCellBound L k I) :
-- imply
  FKIsingExpandingCenteredTopRightBoundaryEdgeBounds L k := by
-- proof
  apply StatMech.Universality.fkIsingExpandingCenteredTopRightBoundaryEdgeBounds_of_diagonal L k hright htop

/--
[fkIsingExpandingCenteredOuterCollarBound_of_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredFourSectorAssembly.lean)
-/
@[path]
private lemma fkIsingExpandingCenteredOuterCollarBound_of_diagonal_eq
  {L : NNReal}
  {k : Nat}
-- given
  (hright : ∀ J, FKIsingExpandingCenteredRightDiagonalCellBound L k J)
  (htop : ∀ I, FKIsingExpandingCenteredTopDiagonalCellBound L k I) :
-- imply
  FKIsingExpandingCenteredOuterCollarBound L k := by
-- proof
  apply StatMech.Universality.fkIsingExpandingCenteredOuterCollarBound_of_diagonal L k hright htop

/--
[fkIsingExpandingCenteredNeighborTransport_of_four_sector_diagonal_and_collar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredFourSectorAssembly.lean)
-/
@[path]
private lemma fkIsingExpandingCenteredNeighborTransport_of_four_sector_diagonal_and_collar_eq
  {L : NNReal}
  {N : Nat}
-- given
  (hN : 1 ≤ N)
  (hdiag : ∀ q : Fin 4, ∀ k, N ≤ k → ∀ i j, isingCenteredRadialIndexSector (fkIsingExpandingSquareSide k) i j = q → FKIsingExpandingCenteredDiagonalCellBound L k i j)
  (hcollar : ∀ k, N ≤ k → FKIsingExpandingCenteredOuterCollarBound L k) :
-- imply
  FKIsingExpandingCenteredNeighborTransport := by
-- proof
  apply StatMech.Universality.fkIsingExpandingCenteredNeighborTransport_of_four_sector_diagonal_and_collar L N hN hdiag hcollar

/--
[fkIsingExpandingCenteredStrictNeighborTransport_of_four_sector_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredFourSectorAssembly.lean)
-/
@[path]
private lemma fkIsingExpandingCenteredStrictNeighborTransport_of_four_sector_diagonal_eq
  {L : NNReal}
  {N : Nat}
-- given
  (hN : 1 ≤ N)
  (hdiag : ∀ q : Fin 4, ∀ k, N ≤ k → ∀ i j, isingCenteredRadialIndexSector (fkIsingExpandingSquareSide k) i j = q → FKIsingExpandingCenteredDiagonalCellBound L k i j) :
-- imply
  FKIsingExpandingCenteredStrictNeighborTransport := by
-- proof
  apply StatMech.Universality.fkIsingExpandingCenteredStrictNeighborTransport_of_four_sector_diagonal L N hN hdiag

/--
[fkIsingExpandingCenteredNeighborTransport_of_four_sector_and_boundary_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredFourSectorAssembly.lean)
-/
@[path]
private lemma fkIsingExpandingCenteredNeighborTransport_of_four_sector_and_boundary_diagonal_eq
  {L : NNReal}
  {N : Nat}
-- given
  (hN : 1 ≤ N)
  (hdiag : ∀ q : Fin 4, ∀ k, N ≤ k → ∀ i j, isingCenteredRadialIndexSector (fkIsingExpandingSquareSide k) i j = q → FKIsingExpandingCenteredDiagonalCellBound L k i j)
  (hright : ∀ k, N ≤ k → ∀ J, FKIsingExpandingCenteredRightDiagonalCellBound L k J)
  (htop : ∀ k, N ≤ k → ∀ I, FKIsingExpandingCenteredTopDiagonalCellBound L k I) :
-- imply
  FKIsingExpandingCenteredNeighborTransport := by
-- proof
  apply StatMech.Universality.fkIsingExpandingCenteredNeighborTransport_of_four_sector_and_boundary_diagonal L N hN hdiag hright htop


-- created on 2026-10-23

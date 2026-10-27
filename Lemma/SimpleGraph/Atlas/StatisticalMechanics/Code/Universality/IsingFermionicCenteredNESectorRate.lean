import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCenteredNESectorRate
open StatMech StatMech.Universality


/--
[fkIsingExpandingBoundarySquareCenteredNE_window_indices_lt_outer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredNESectorRate.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquareCenteredNE_window_indices_lt_outer_eq
  {k baseI baseJ R : Nat}
  {p : IsingLeapfrogBox R}
-- given
  (hfitI : baseI + R + 1 < fkIsingExpandingSquareSide k)
  (hfitJ : baseJ + R + 1 < fkIsingExpandingSquareSide k) :
-- imply
  fkIsingExpandingSquareSide k + (baseI + p.1.1) + 1 < 2 * fkIsingExpandingSquareSide k ∧ fkIsingExpandingSquareSide k + (baseJ + p.2.1) + 1 < 2 * fkIsingExpandingSquareSide k := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquareCenteredNE_window_indices_lt_outer k baseI baseJ R hfitI hfitJ p

/--
[fkIsingExpandingBoundarySquareCenteredNE_normalizedNeighbor_norm_sub_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredNESectorRate.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquareCenteredNE_normalizedNeighbor_norm_sub_le_eq
  {k baseI baseJ R rho cutoff : Nat}
  {p p' : IsingLeapfrogBox R}
-- given
  (hk : 1 <= k)
  (hfitI : baseI + R + 1 < fkIsingExpandingSquareSide k)
  (hfitJ : baseJ + R + 1 < fkIsingExpandingSquareSide k)
  (hcutoff : 0 < cutoff)
  (hdeep : forall q : IsingLeapfrogBox R, fkIsingSquareRadialPatchWindowCell (fkIsingExpandingSquareSide k) baseI baseJ R hfitI hfitJ q ∈ fkIsingSquareRadialPatchDeepCells (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide k) (le_refl _) (by simp only [fkIsingExpandingSquareSide, pow_two] nlinarith) cutoff)
  (hsideCutoff : fkIsingExpandingSquareSide k <= 4 * cutoff)
  (hsideRho : fkIsingExpandingSquareSide k <= 4 * rho)
  (hrho : 0 < rho)
  (hp : IsingLeapfrogInteriorMargin R rho p)
  (hp' : IsingLeapfrogInteriorMargin R rho p')
  (hpp' : IsingLeapfrogDiagonalAdjacent p p') :
-- imply
  norm (fkIsingSquareBoundaryCenteredRadialPatchFullObservable (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k) ⟨fkIsingExpandingSquareSide k + (baseI + p.1.1), by have := p.1.2 omega⟩ ⟨fkIsingExpandingSquareSide k + (baseJ + p.2.1), by have := p.2.2 omega⟩ / (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex) - fkIsingSquareBoundaryCenteredRadialPatchFullObservable (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k) ⟨fkIsingExpandingSquareSide k + (baseI + p'.1.1), by have := p'.1.2 omega⟩ ⟨fkIsingExpandingSquareSide k + (baseJ + p'.2.1), by have := p'.2.2 omega⟩ / (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) <= fkIsingExpandingSquareScale k * 40000 := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquareCenteredNE_normalizedNeighbor_norm_sub_le k baseI baseJ R rho cutoff hk hfitI hfitJ hcutoff hdeep hsideCutoff hsideRho p p' hrho hp hp' hpp'


-- created on 2026-10-23

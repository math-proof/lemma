import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicCenteredTVRegularity
open StatMech StatMech.Universality


/--
[fkIsingSquareBoundaryCenteredRadialPatchFullObservable_cell_edges_le_of_margin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTVRegularity.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryCenteredRadialPatchFullObservable_cell_edges_le_of_margin_eq
  {n i j rho : Nat}
  {mesh : Real}
-- given
  (hn : 0 < n)
  (hi0 : 0 < i)
  (hi1 : i + 1 < 2 * n)
  (hj0 : 0 < j)
  (hj1 : j + 1 < 2 * n)
  (hrho : 0 < rho)
  (hmesh : 0 < mesh)
  (hiLeft : rho ≤ i - 1)
  (hiRight : i + rho ≤ 2 * n - 2)
  (hjBottom : rho ≤ j - 1)
  (hjTop : j + rho ≤ 2 * n - 2) :
-- imply
  let north := fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨i, by omega⟩ ⟨j - 1, by omega⟩ let east := fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨i, by omega⟩ ⟨j, by omega⟩ let south := fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨i - 1, by omega⟩ ⟨j, by omega⟩ let west := fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ ‖north / (Real.sqrt (2 * mesh) : Complex) - east / (Real.sqrt (2 * mesh) : Complex)‖ ≤ 608 / ((rho : Real) * Real.sqrt (2 * mesh)) ∧ ‖east / (Real.sqrt (2 * mesh) : Complex) - south / (Real.sqrt (2 * mesh) : Complex)‖ ≤ 608 / ((rho : Real) * Real.sqrt (2 * mesh)) ∧ ‖south / (Real.sqrt (2 * mesh) : Complex) - west / (Real.sqrt (2 * mesh) : Complex)‖ ≤ 608 / ((rho : Real) * Real.sqrt (2 * mesh)) ∧ ‖west / (Real.sqrt (2 * mesh) : Complex) - north / (Real.sqrt (2 * mesh) : Complex)‖ ≤ 608 / ((rho : Real) * Real.sqrt (2 * mesh)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryCenteredRadialPatchFullObservable_cell_edges_le_of_margin n i j rho mesh hn hi0 hi1 hj0 hj1 hrho hmesh hiLeft hiRight hjBottom hjTop

/--
[closedBall_subset_finiteCenteredRadialGridMarginInterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTVRegularity.lean)
-/
@[path]
private lemma closedBall_subset_finiteCenteredRadialGridMarginInterior_eq
  {n rho : Nat}
  {mesh R : Real}
-- given
  (hmesh : 0 < mesh)
  (hR : 0 ≤ R)
  (hwide : 2 * R + ((rho : Real) + 6) * mesh ≤ mesh * n) :
-- imply
  closedBall (0 : Complex) R ⊆ finiteCenteredRadialGridMarginInterior n rho mesh := by
-- proof
  apply StatMech.Universality.closedBall_subset_finiteCenteredRadialGridMarginInterior n rho mesh R hmesh hR hwide

/--
[finiteCenteredRadialGridInterpolant_lipschitzOnWith_of_fullCarrierTV](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTVRegularity.lean)
-/
@[path]
private lemma finiteCenteredRadialGridInterpolant_lipschitzOnWith_of_fullCarrierTV_eq
  {n rho : Nat}
  {gridScale normalizationScale : Real}
  {s : Set Complex}
  {L : NNReal}
-- given
  (hn : 0 < n)
  (hgridScale : 0 < gridScale)
  (hnormalizationScale : 0 < normalizationScale)
  (hrho : 0 < rho)
  (hs : Convex Real s)
  (hinside : s ⊆ finiteCenteredRadialGridMarginInterior n rho gridScale)
  (hTV : 608 / ((rho : Real) * Real.sqrt (2 * normalizationScale)) ≤ gridScale * (L : Real)) :
-- imply
  LipschitzOnWith (4 * L) (finiteCenteredRadialGridInterpolant n gridScale (fun i j ↦ fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn i j / (Real.sqrt (2 * normalizationScale) : Complex))) s := by
-- proof
  apply StatMech.Universality.finiteCenteredRadialGridInterpolant_lipschitzOnWith_of_fullCarrierTV n rho gridScale normalizationScale hn hgridScale hnormalizationScale hrho s hs L hinside hTV

/--
[fkIsingExpandingSquare_fullCarrierTVCoefficient_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTVRegularity.lean)
-/
@[path]
private lemma fkIsingExpandingSquare_fullCarrierTVCoefficient_le_eq
  {k : Nat}
-- given
  (hk : 2 ≤ k) :
-- imply
  let rho := (k / 2) * (k + 1) 608 / ((rho : Real) * Real.sqrt (2 * fkIsingExpandingSquareMesh k)) ≤ fkIsingExpandingSquareScale k * 2432 := by
-- proof
  apply StatMech.Universality.fkIsingExpandingSquare_fullCarrierTVCoefficient_le k hk

/--
[fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_lipschitzOnWith_closedBall_of_fullCarrierTV](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTVRegularity.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_lipschitzOnWith_closedBall_of_fullCarrierTV_eq
  {k : Nat}
  {R : Real}
-- given
  (hR : 0 ≤ R)
  (hk : 2 ≤ k)
  (hwide : 2 * R + ((((k / 2) * (k + 1) : Nat) : Real) + 6) * fkIsingExpandingSquareScale k ≤ fkIsingExpandingSquareScale k * fkIsingExpandingSquareSide k) :
-- imply
  LipschitzOnWith (4 * (2432 : NNReal)) (fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k) (closedBall (0 : Complex) R) := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_lipschitzOnWith_closedBall_of_fullCarrierTV k R hR hk hwide

/--
[fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_meshUniformCompactHolder_fullCarrierTV](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTVRegularity.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_meshUniformCompactHolder_fullCarrierTV_eq :
-- imply
  fkIsingExpandingBoundarySquareCaratheodoryApproximation.MeshUniformCompactHolder fkIsingExpandingBoundarySquareCenteredReflectedInterpolant := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_meshUniformCompactHolder_fullCarrierTV


-- created on 2026-10-23

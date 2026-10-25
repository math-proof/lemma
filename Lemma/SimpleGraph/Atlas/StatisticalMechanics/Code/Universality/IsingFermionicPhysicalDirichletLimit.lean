import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDirichletLimit.Part2
open Filter Set Topology StatMech StatMech.Universality


/--
[fkIsingSquare_discreteDirichlet_uniform_convergence_to_imPhi_of_barrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalDirichletLimit.lean)
-/
@[path]
private lemma fkIsingSquare_discreteDirichlet_uniform_convergence_to_imPhi_of_barrier_eq
  {Phi : Complex → Complex}
  {boundaryError residual barrierBound : Nat → Real}
-- given
  (embedding : ∀ n, (fkSquareBoxPlanar n).V → Complex)
  (harmonic barrier : ∀ n, (fkSquareBoxPlanar n).V → Real)
  (hharmonic : ∀ n, IsingFiniteGraphHarmonicOn (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n) (harmonic n))
  (hboundary : ∀ n x, fkIsingSquareBoxBoundary n x → |harmonic n x - fkIsingSquareSampledImaginaryPart embedding Phi n x| ≤ boundaryError n)
  (hresidual_nonneg : ∀ n, 0 ≤ residual n)
  (hbarrier_nonneg : ∀ n x, 0 ≤ barrier n x)
  (hbarrier_bound : ∀ n x, barrier n x ≤ barrierBound n)
  (hbarrier_laplacian : ∀ n x, ¬ fkIsingSquareBoxBoundary n x → isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G (barrier n) x ≤ -1)
  (htarget_residual : ∀ n x, ¬ fkIsingSquareBoxBoundary n x → |isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G (fkIsingSquareSampledImaginaryPart embedding Phi n) x| ≤ residual n)
  (herror : Tendsto (fun n ↦ boundaryError n + residual n * barrierBound n) atTop (nhds 0)) :
-- imply
  ∀ eta : Real, 0 < eta → ∀ᶠ n in atTop, ∀ x, := by
-- proof
  apply StatMech.Universality.fkIsingSquare_discreteDirichlet_uniform_convergence_to_imPhi_of_barrier embedding Phi harmonic barrier boundaryError residual barrierBound hharmonic hboundary hresidual_nonneg hbarrier_nonneg hbarrier_bound hbarrier_laplacian htarget_residual herror

/--
[fkIsingSquare_discreteDirichlet_uniform_convergence_to_imPhi_of_consistency](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalDirichletLimit.lean)
-/
@[path]
private lemma fkIsingSquare_discreteDirichlet_uniform_convergence_to_imPhi_of_consistency_eq
  {Phi : Complex → Complex}
  {boundaryError residual : Nat → Real}
-- given
  (embedding : ∀ n, (fkSquareBoxPlanar n).V → Complex)
  (harmonic : ∀ n, (fkSquareBoxPlanar n).V → Real)
  (hharmonic : ∀ n, IsingFiniteGraphHarmonicOn (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n) (harmonic n))
  (hboundary : ∀ n x, fkIsingSquareBoxBoundary n x → |harmonic n x - fkIsingSquareSampledImaginaryPart embedding Phi n x| ≤ boundaryError n)
  (hresidual_nonneg : ∀ n, 0 ≤ residual n)
  (htarget_residual : ∀ n x, ¬ fkIsingSquareBoxBoundary n x → |isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G (fkIsingSquareSampledImaginaryPart embedding Phi n) x| ≤ residual n)
  (herror : Tendsto (fun n ↦ boundaryError n + residual n * fkIsingSquareBoxPoissonBarrierBound n) atTop (nhds 0)) :
-- imply
  ∀ eta : Real, 0 < eta → ∀ᶠ n in atTop, ∀ x, := by
-- proof
  apply StatMech.Universality.fkIsingSquare_discreteDirichlet_uniform_convergence_to_imPhi_of_consistency embedding Phi harmonic boundaryError residual hharmonic hboundary hresidual_nonneg htarget_residual herror

/--
[fkIsingSquare_discreteDirichlet_uniform_convergence_to_imPhi_of_quadratic_rate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalDirichletLimit.lean)
-/
@[path]
private lemma fkIsingSquare_discreteDirichlet_uniform_convergence_to_imPhi_of_quadratic_rate_eq
  {Phi : Complex → Complex}
  {boundaryError residual : Nat → Real}
-- given
  (embedding : ∀ n, (fkSquareBoxPlanar n).V → Complex)
  (harmonic : ∀ n, (fkSquareBoxPlanar n).V → Real)
  (hharmonic : ∀ n, IsingFiniteGraphHarmonicOn (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n) (harmonic n))
  (hboundary : ∀ n x, fkIsingSquareBoxBoundary n x → |harmonic n x - fkIsingSquareSampledImaginaryPart embedding Phi n x| ≤ boundaryError n)
  (hresidual_nonneg : ∀ n, 0 ≤ residual n)
  (htarget_residual : ∀ n x, ¬ fkIsingSquareBoxBoundary n x → |isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G (fkIsingSquareSampledImaginaryPart embedding Phi n) x| ≤ residual n)
  (herror : Tendsto (fun n ↦ boundaryError n + residual n * ((n : Real) ^ 2 / 2)) atTop (nhds 0)) :
-- imply
  ∀ eta : Real, 0 < eta → ∀ᶠ n in atTop, ∀ x, := by
-- proof
  apply StatMech.Universality.fkIsingSquare_discreteDirichlet_uniform_convergence_to_imPhi_of_quadratic_rate embedding Phi harmonic boundaryError residual hharmonic hboundary hresidual_nonneg htarget_residual herror

/--
[fkIsingSquare_physicalPrimitive_uniform_convergence_to_imPhi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalDirichletLimit.lean)
-/
@[path]
private lemma fkIsingSquare_physicalPrimitive_uniform_convergence_to_imPhi_eq
  {Phi : Complex → Complex}
  {eps : Nat → Real}
-- given
  (embedding : ∀ n, (fkSquareBoxPlanar n).V → Complex)
  (upper lower harmonic physical : ∀ n, (fkSquareBoxPlanar n).V → Real)
  (hupper : ∀ n, IsingFiniteGraphSubharmonicOn (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n) (upper n))
  (hlower : ∀ n, IsingFiniteGraphSuperharmonicOn (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n) (lower n))
  (hharmonic : ∀ n, IsingFiniteGraphHarmonicOn (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n) (harmonic n))
  (hupperBoundary : ∀ n x, fkIsingSquareBoxBoundary n x → upper n x ≤ harmonic n x + eps n)
  (hlowerBoundary : ∀ n x, fkIsingSquareBoxBoundary n x → harmonic n x ≤ lower n x + eps n)
  (hsandwich : ∀ n x, lower n x ≤ physical n x ∧ physical n x ≤ upper n x)
  (heps : Tendsto eps atTop (nhds 0))
  (hdirichlet : ∀ eta : Real, 0 < eta → ∀ᶠ n in atTop, ∀ x, |harmonic n x - fkIsingSquareSampledImaginaryPart embedding Phi n x| < eta) :
-- imply
  ∀ eta : Real, 0 < eta → ∀ᶠ n in atTop, ∀ x, := by
-- proof
  apply StatMech.Universality.fkIsingSquare_physicalPrimitive_uniform_convergence_to_imPhi embedding Phi upper lower harmonic physical eps hupper hlower hharmonic hupperBoundary hlowerBoundary hsandwich heps hdirichlet


-- created on 2026-10-23

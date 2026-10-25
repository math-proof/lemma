import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareDirichletConvergence.Part3
open Finset SimpleGraph Filter Set Topology StatMech StatMech.Universality


/--
[fkIsingSquareMarkedA_mem_boxBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareDirichletConvergence.lean)
-/
@[path]
private lemma fkIsingSquareMarkedA_mem_boxBoundary_eq
  {n : Nat} :
-- imply
  fkIsingSquareBoxBoundary n (fkIsingSquareMarkedA n) := by
-- proof
  apply StatMech.Universality.fkIsingSquareMarkedA_mem_boxBoundary n

/--
[fkIsingSquareBox_reachable_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareDirichletConvergence.lean)
-/
@[path]
private lemma fkIsingSquareBox_reachable_boundary_eq
  {n : Nat} :
-- imply
  ∀ x : (fkSquareBoxPlanar n).V, ∃ b, fkIsingSquareBoxBoundary n b ∧ (fkSquareBoxPlanar n).G.Reachable x b := by
-- proof
  apply StatMech.Universality.fkIsingSquareBox_reachable_boundary n

/--
[fkIsingSquareBoxQuadraticBarrier_laplacian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareDirichletConvergence.lean)
-/
@[path]
private lemma fkIsingSquareBoxQuadraticBarrier_laplacian_eq
  {n : Nat}
  {x : (fkSquareBoxPlanar n).V}
-- given
  (hx : ¬ fkIsingSquareBoxBoundary n x) :
-- imply
  isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G (fkIsingSquareBoxQuadraticBarrier n) x = -1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoxQuadraticBarrier_laplacian n x hx

/--
[fkIsingSquareBoxQuadraticBarrier_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareDirichletConvergence.lean)
-/
@[path]
private lemma fkIsingSquareBoxQuadraticBarrier_nonneg_eq
  {n : Nat}
  {x : (fkSquareBoxPlanar n).V} :
-- imply
  0 ≤ fkIsingSquareBoxQuadraticBarrier n x := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoxQuadraticBarrier_nonneg n x

/--
[fkIsingSquareBoxQuadraticBarrier_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareDirichletConvergence.lean)
-/
@[path]
private lemma fkIsingSquareBoxQuadraticBarrier_le_eq
  {n : Nat}
  {x : (fkSquareBoxPlanar n).V} :
-- imply
  fkIsingSquareBoxQuadraticBarrier n x ≤ (n : Real) ^ 2 / 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoxQuadraticBarrier_le n x

/--
[fkIsingSquareBoxPoissonBarrier_le_quadratic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareDirichletConvergence.lean)
-/
@[path]
private lemma fkIsingSquareBoxPoissonBarrier_le_quadratic_eq
  {n : Nat} :
-- imply
  ∀ x, fkIsingSquareBoxCanonicalPoissonBarrier n x ≤ fkIsingSquareBoxQuadraticBarrier n x := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoxPoissonBarrier_le_quadratic n

/--
[fkIsingSquareBoxPoissonBarrierBound_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareDirichletConvergence.lean)
-/
@[path]
private lemma fkIsingSquareBoxPoissonBarrierBound_le_eq
  {n : Nat} :
-- imply
  fkIsingSquareBoxCanonicalPoissonBarrierBound n ≤ (n : Real) ^ 2 / 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoxPoissonBarrierBound_le n

/--
[fkIsingSquare_harmonic_boundary_stability](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareDirichletConvergence.lean)
-/
@[path]
private lemma fkIsingSquare_harmonic_boundary_stability_eq
  {n : Nat}
  {u v : (fkSquareBoxPlanar n).V → Real}
  {eps : Real}
-- given
  (hu : IsingFiniteGraphHarmonicOn (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n) u)
  (hv : IsingFiniteGraphHarmonicOn (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n) v)
  (hboundary : ∀ x, fkIsingSquareBoxBoundary n x → |u x - v x| ≤ eps) :
-- imply
  ∀ x, := by
-- proof
  apply StatMech.Universality.fkIsingSquare_harmonic_boundary_stability n u v eps hu hv hboundary

/--
[fkIsingSquare_dirichlet_sandwich_stability](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareDirichletConvergence.lean)
-/
@[path]
private lemma fkIsingSquare_dirichlet_sandwich_stability_eq
  {n : Nat}
  {eps : Real}
-- given
  (upper lower harmonic f : (fkSquareBoxPlanar n).V → Real)
  (hupper : IsingFiniteGraphSubharmonicOn (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n) upper)
  (hlower : IsingFiniteGraphSuperharmonicOn (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n) lower)
  (hharmonic : IsingFiniteGraphHarmonicOn (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n) harmonic)
  (hupperBoundary : ∀ x, fkIsingSquareBoxBoundary n x → upper x ≤ harmonic x + eps)
  (hlowerBoundary : ∀ x, fkIsingSquareBoxBoundary n x → harmonic x ≤ lower x + eps)
  (hsandwich : ∀ x, lower x ≤ f x ∧ f x ≤ upper x) :
-- imply
  ∀ x, := by
-- proof
  apply StatMech.Universality.fkIsingSquare_dirichlet_sandwich_stability n upper lower harmonic f eps hupper hlower hharmonic hupperBoundary hlowerBoundary hsandwich

/--
[fkIsingSquare_harmonic_uniform_convergence_of_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareDirichletConvergence.lean)
-/
@[path]
private lemma fkIsingSquare_harmonic_uniform_convergence_of_boundary_eq
  {eps : Nat → Real}
-- given
  (u v : ∀ n, (fkSquareBoxPlanar n).V → Real)
  (hu : ∀ n, IsingFiniteGraphHarmonicOn (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n) (u n))
  (hv : ∀ n, IsingFiniteGraphHarmonicOn (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n) (v n))
  (hboundary : ∀ n x, fkIsingSquareBoxBoundary n x → |u n x - v n x| ≤ eps n)
  (heps : Tendsto eps atTop (nhds 0)) :
-- imply
  ∀ eta : Real, 0 < eta → ∀ᶠ n in atTop, ∀ x, := by
-- proof
  apply StatMech.Universality.fkIsingSquare_harmonic_uniform_convergence_of_boundary u v eps hu hv hboundary heps

/--
[fkIsingSquare_dirichlet_sandwich_uniform_convergence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareDirichletConvergence.lean)
-/
@[path]
private lemma fkIsingSquare_dirichlet_sandwich_uniform_convergence_eq
  {eps : Nat → Real}
-- given
  (upper lower harmonic f : ∀ n, (fkSquareBoxPlanar n).V → Real)
  (hupper : ∀ n, IsingFiniteGraphSubharmonicOn (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n) (upper n))
  (hlower : ∀ n, IsingFiniteGraphSuperharmonicOn (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n) (lower n))
  (hharmonic : ∀ n, IsingFiniteGraphHarmonicOn (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n) (harmonic n))
  (hupperBoundary : ∀ n x, fkIsingSquareBoxBoundary n x → upper n x ≤ harmonic n x + eps n)
  (hlowerBoundary : ∀ n x, fkIsingSquareBoxBoundary n x → harmonic n x ≤ lower n x + eps n)
  (hsandwich : ∀ n x, lower n x ≤ f n x ∧ f n x ≤ upper n x)
  (heps : Tendsto eps atTop (nhds 0)) :
-- imply
  ∀ eta : Real, 0 < eta → ∀ᶠ n in atTop, ∀ x, := by
-- proof
  apply StatMech.Universality.fkIsingSquare_dirichlet_sandwich_uniform_convergence upper lower harmonic f eps hupper hlower hharmonic hupperBoundary hlowerBoundary hsandwich heps


-- created on 2026-10-23

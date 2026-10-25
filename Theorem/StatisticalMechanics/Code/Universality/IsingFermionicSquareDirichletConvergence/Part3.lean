/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareDirichletConvergence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDirichletComparison.Part5
import Theorem.StatisticalMechanics.Code.FrontierB.BoxGraphPath.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareDirichletConvergence.Part3
open Finset SimpleGraph Filter Set Topology


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareBoxPoissonBarrier_le_quadratic
    (n : Nat) : ∀ x,
    fkIsingSquareBoxCanonicalPoissonBarrier n x ≤
      fkIsingSquareBoxQuadraticBarrier n x := by
  letI : Nonempty (fkSquareBoxPlanar n).V :=
    ⟨fkIsingSquareMarkedA n⟩
  change ∀ x, isingFiniteGraphPoissonBarrier
      (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n)
      (fkIsingSquareBox_reachable_boundary n) x ≤
    fkIsingSquareBoxQuadraticBarrier n x
  apply isingFiniteGraph_laplacian_comparison
    (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n)
    (isingFiniteGraphPoissonBarrier
      (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n)
      (fkIsingSquareBox_reachable_boundary n))
    (fkIsingSquareBoxQuadraticBarrier n)
    (fkIsingSquareBox_reachable_boundary n)
  · intro x hx
    rw [isingFiniteGraphPoissonBarrier_boundary
      (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n)
      (fkIsingSquareBox_reachable_boundary n) x hx]
    exact fkIsingSquareBoxQuadraticBarrier_nonneg n x
  · intro x hx
    rw [fkIsingSquareBoxQuadraticBarrier_laplacian n x hx,
      isingFiniteGraphPoissonBarrier_laplacian
        (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n)
        (fkIsingSquareBox_reachable_boundary n) x hx]


theorem fkIsingSquareBoxPoissonBarrierBound_le (n : Nat) :
    fkIsingSquareBoxCanonicalPoissonBarrierBound n ≤
      (n : Real) ^ 2 / 2 := by
  letI : Nonempty (fkSquareBoxPlanar n).V :=
    ⟨fkIsingSquareMarkedA n⟩
  change isingFiniteGraphPoissonBarrierBound
      (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n)
      (fkIsingSquareBox_reachable_boundary n) ≤ (n : Real) ^ 2 / 2
  unfold isingFiniteGraphPoissonBarrierBound
  rw [Finset.max'_le_iff]
  intro z hz
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hz
  exact (fkIsingSquareBoxPoissonBarrier_le_quadratic n x).trans
    (fkIsingSquareBoxQuadraticBarrier_le n x)


theorem fkIsingSquare_harmonic_boundary_stability
    (n : Nat) (u v : (fkSquareBoxPlanar n).V → Real) (eps : Real)
    (hu : IsingFiniteGraphHarmonicOn (fkSquareBoxPlanar n).G
      (fkIsingSquareBoxBoundary n) u)
    (hv : IsingFiniteGraphHarmonicOn (fkSquareBoxPlanar n).G
      (fkIsingSquareBoxBoundary n) v)
    (hboundary : ∀ x, fkIsingSquareBoxBoundary n x →
      |u x - v x| ≤ eps) :
    ∀ x, |u x - v x| ≤ eps := by
  letI : Nonempty (fkSquareBoxPlanar n).V :=
    ⟨fkIsingSquareMarkedA n⟩
  exact isingFiniteGraph_harmonic_boundary_stability
    (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n)
      u v eps (fkIsingSquareBox_reachable_boundary n) hu hv hboundary


theorem fkIsingSquare_dirichlet_sandwich_stability
    (n : Nat) (upper lower harmonic f : (fkSquareBoxPlanar n).V → Real)
    (eps : Real)
    (hupper : IsingFiniteGraphSubharmonicOn (fkSquareBoxPlanar n).G
      (fkIsingSquareBoxBoundary n) upper)
    (hlower : IsingFiniteGraphSuperharmonicOn (fkSquareBoxPlanar n).G
      (fkIsingSquareBoxBoundary n) lower)
    (hharmonic : IsingFiniteGraphHarmonicOn (fkSquareBoxPlanar n).G
      (fkIsingSquareBoxBoundary n) harmonic)
    (hupperBoundary : ∀ x, fkIsingSquareBoxBoundary n x →
      upper x ≤ harmonic x + eps)
    (hlowerBoundary : ∀ x, fkIsingSquareBoxBoundary n x →
      harmonic x ≤ lower x + eps)
    (hsandwich : ∀ x, lower x ≤ f x ∧ f x ≤ upper x) :
    ∀ x, |f x - harmonic x| ≤ eps := by
  letI : Nonempty (fkSquareBoxPlanar n).V :=
    ⟨fkIsingSquareMarkedA n⟩
  have hup : ∀ x, upper x ≤ harmonic x + eps := by
    apply isingFiniteGraph_subharmonic_le_harmonic
      (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n)
      upper (fun x ↦ harmonic x + eps)
      (fkIsingSquareBox_reachable_boundary n) hupper
      (hharmonic.add_const eps) hupperBoundary
  have hlo : ∀ x, harmonic x ≤ lower x + eps := by
    apply isingFiniteGraph_harmonic_le_superharmonic
      (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n)
      harmonic (fun x ↦ lower x + eps)
      (fkIsingSquareBox_reachable_boundary n) hharmonic
    · intro x hx
      rw [isingFiniteGraphLaplacian_add_const]
      exact hlower x hx
    · exact hlowerBoundary
  intro x
  rw [abs_le]
  rcases hsandwich x with ⟨hxf, hfx⟩
  constructor <;> linarith [hup x, hlo x]


theorem fkIsingSquare_harmonic_uniform_convergence_of_boundary
    (u v : ∀ n, (fkSquareBoxPlanar n).V → Real)
    (eps : Nat → Real)
    (hu : ∀ n, IsingFiniteGraphHarmonicOn (fkSquareBoxPlanar n).G
      (fkIsingSquareBoxBoundary n) (u n))
    (hv : ∀ n, IsingFiniteGraphHarmonicOn (fkSquareBoxPlanar n).G
      (fkIsingSquareBoxBoundary n) (v n))
    (hboundary : ∀ n x, fkIsingSquareBoxBoundary n x →
      |u n x - v n x| ≤ eps n)
    (heps : Tendsto eps atTop (nhds 0)) :
    ∀ eta : Real, 0 < eta →
      ∀ᶠ n in atTop, ∀ x, |u n x - v n x| < eta := by
  intro eta heta
  have hevent : ∀ᶠ n in atTop, eps n < eta :=
    heps (Iio_mem_nhds heta)
  filter_upwards [hevent] with n hn
  intro x
  exact lt_of_le_of_lt
    (fkIsingSquare_harmonic_boundary_stability n (u n) (v n)
      (eps n) (hu n) (hv n) (hboundary n) x) hn


theorem fkIsingSquare_dirichlet_sandwich_uniform_convergence
    (upper lower harmonic f : ∀ n, (fkSquareBoxPlanar n).V → Real)
    (eps : Nat → Real)
    (hupper : ∀ n, IsingFiniteGraphSubharmonicOn (fkSquareBoxPlanar n).G
      (fkIsingSquareBoxBoundary n) (upper n))
    (hlower : ∀ n, IsingFiniteGraphSuperharmonicOn (fkSquareBoxPlanar n).G
      (fkIsingSquareBoxBoundary n) (lower n))
    (hharmonic : ∀ n, IsingFiniteGraphHarmonicOn (fkSquareBoxPlanar n).G
      (fkIsingSquareBoxBoundary n) (harmonic n))
    (hupperBoundary : ∀ n x, fkIsingSquareBoxBoundary n x →
      upper n x ≤ harmonic n x + eps n)
    (hlowerBoundary : ∀ n x, fkIsingSquareBoxBoundary n x →
      harmonic n x ≤ lower n x + eps n)
    (hsandwich : ∀ n x, lower n x ≤ f n x ∧ f n x ≤ upper n x)
    (heps : Tendsto eps atTop (nhds 0)) :
    ∀ eta : Real, 0 < eta →
      ∀ᶠ n in atTop, ∀ x, |f n x - harmonic n x| < eta := by
  intro eta heta
  have hevent : ∀ᶠ n in atTop, eps n < eta :=
    heps (Iio_mem_nhds heta)
  filter_upwards [hevent] with n hn
  intro x
  exact lt_of_le_of_lt
    (fkIsingSquare_dirichlet_sandwich_stability n
      (upper n) (lower n) (harmonic n) (f n) (eps n)
      (hupper n) (hlower n) (hharmonic n)
      (hupperBoundary n) (hlowerBoundary n) (hsandwich n) x) hn

end
end StatMech.Universality

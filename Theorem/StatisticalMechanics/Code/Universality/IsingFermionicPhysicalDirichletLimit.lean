/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalDirichletLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareDirichletConvergence.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalEnergy
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDirichletLimit
open Filter Set Topology


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquare_discreteDirichlet_uniform_convergence_to_imPhi_of_barrier
    (embedding : ∀ n, (fkSquareBoxPlanar n).V → Complex)
    (Phi : Complex → Complex)
    (harmonic barrier : ∀ n, (fkSquareBoxPlanar n).V → Real)
    (boundaryError residual barrierBound : Nat → Real)
    (hharmonic : ∀ n, IsingFiniteGraphHarmonicOn
      (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n) (harmonic n))
    (hboundary : ∀ n x, fkIsingSquareBoxBoundary n x →
      |harmonic n x - fkIsingSquareSampledImaginaryPart
        embedding Phi n x| ≤ boundaryError n)
    (hresidual_nonneg : ∀ n, 0 ≤ residual n)
    (hbarrier_nonneg : ∀ n x, 0 ≤ barrier n x)
    (hbarrier_bound : ∀ n x, barrier n x ≤ barrierBound n)
    (hbarrier_laplacian : ∀ n x, ¬ fkIsingSquareBoxBoundary n x →
      isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G (barrier n) x ≤ -1)
    (htarget_residual : ∀ n x, ¬ fkIsingSquareBoxBoundary n x →
      |isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
        (fkIsingSquareSampledImaginaryPart embedding Phi n) x| ≤ residual n)
    (herror : Tendsto
      (fun n ↦ boundaryError n + residual n * barrierBound n)
      atTop (nhds 0)) :
    ∀ eta : Real, 0 < eta →
      ∀ᶠ n in atTop, ∀ x,
        |harmonic n x - fkIsingSquareSampledImaginaryPart
          embedding Phi n x| < eta := by
  intro eta heta
  have hevent : ∀ᶠ n in atTop,
      boundaryError n + residual n * barrierBound n < eta :=
    herror (Iio_mem_nhds heta)
  filter_upwards [hevent] with n hn
  intro x
  letI : Nonempty (fkSquareBoxPlanar n).V :=
    ⟨fkIsingSquareMarkedA n⟩
  exact lt_of_le_of_lt
    (isingFiniteGraph_harmonic_approximation_of_barrier
      (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n)
      (harmonic n) (fkIsingSquareSampledImaginaryPart embedding Phi n)
      (barrier n) (boundaryError n) (residual n) (barrierBound n)
      (fkIsingSquareBox_reachable_boundary n) (hharmonic n)
      (hboundary n) (hresidual_nonneg n) (hbarrier_nonneg n)
      (hbarrier_bound n) (hbarrier_laplacian n) (htarget_residual n) x)
    hn


end
end StatMech.Universality

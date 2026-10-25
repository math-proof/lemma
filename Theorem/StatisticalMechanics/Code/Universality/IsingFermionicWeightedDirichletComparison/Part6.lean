/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWeightedDirichletComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDirichletComparison.Part5
import Def.StatisticalMechanics.Code.Universality.IsingFermionicWeightedDirichletComparison.Part6
open Finset SimpleGraph


namespace StatMech.Universality

noncomputable section

theorem isingFiniteWeightedSpatialResidualPotential_boundary
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V → V → Real)
    (boundary : V → Prop)
    (hconductance : ∀ x y, 0 ≤ conductance x y)
    (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (residual : V → Real) (x : V) (hx : boundary x) :
    isingFiniteWeightedSpatialResidualPotential G conductance boundary
      hconductance hpositive hhit residual x = 0 := by
  classical
  have h := congrFun (isingFiniteWeightedDirichletOperator_solve
    G conductance boundary hconductance hpositive hhit
      (fun y ↦ if boundary y then 0 else -residual y)) x
  change (if boundary x then
      isingFiniteWeightedSpatialResidualPotential G conductance boundary
        hconductance hpositive hhit residual x else
      isingFiniteWeightedLaplacian conductance
        (isingFiniteWeightedSpatialResidualPotential G conductance boundary
          hconductance hpositive hhit residual) x) =
    (if boundary x then 0 else -residual x) at h
  simpa [hx] using h

theorem isingFiniteWeightedSpatialResidualPotential_laplacian
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V → V → Real)
    (boundary : V → Prop)
    (hconductance : ∀ x y, 0 ≤ conductance x y)
    (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (residual : V → Real) (x : V) (hx : ¬ boundary x) :
    isingFiniteWeightedLaplacian conductance
      (isingFiniteWeightedSpatialResidualPotential G conductance boundary
        hconductance hpositive hhit residual) x = -residual x := by
  classical
  have h := congrFun (isingFiniteWeightedDirichletOperator_solve
    G conductance boundary hconductance hpositive hhit
      (fun y ↦ if boundary y then 0 else -residual y)) x
  change (if boundary x then
      isingFiniteWeightedSpatialResidualPotential G conductance boundary
        hconductance hpositive hhit residual x else
      isingFiniteWeightedLaplacian conductance
        (isingFiniteWeightedSpatialResidualPotential G conductance boundary
          hconductance hpositive hhit residual) x) =
    (if boundary x then 0 else -residual x) at h
  simpa [hx] using h

theorem isingFiniteWeightedSpatialResidualPotential_nonneg
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V → V → Real)
    (boundary : V → Prop)
    (hconductance : ∀ x y, 0 ≤ conductance x y)
    (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (residual : V → Real) (hresidual : ∀ x, 0 ≤ residual x) :
    ∀ x, 0 ≤ isingFiniteWeightedSpatialResidualPotential
      G conductance boundary hconductance hpositive hhit residual x := by
  apply isingFiniteWeighted_const_le_superharmonic
    G conductance boundary
    (isingFiniteWeightedSpatialResidualPotential G conductance boundary
      hconductance hpositive hhit residual) 0
    hconductance hpositive hhit
  · intro x hx
    rw [isingFiniteWeightedSpatialResidualPotential_laplacian
      G conductance boundary hconductance hpositive hhit residual x hx]
    exact neg_nonpos.mpr (hresidual x)
  · intro x hx
    rw [isingFiniteWeightedSpatialResidualPotential_boundary
      G conductance boundary hconductance hpositive hhit residual x hx]


theorem isingFiniteWeighted_harmonic_approximation_of_spatial_residual
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V → V → Real)
    (boundary : V → Prop) (harmonic target : V → Real)
    (boundaryError : Real) (residual : V → Real)
    (hconductance : ∀ x y, 0 ≤ conductance x y)
    (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (hharmonic : IsingFiniteWeightedHarmonicOn
      conductance boundary harmonic)
    (hboundary : ∀ x, boundary x →
      |harmonic x - target x| ≤ boundaryError)
    (hresidual_nonneg : ∀ x, 0 ≤ residual x)
    (htarget_residual : ∀ x, ¬ boundary x →
      |isingFiniteWeightedLaplacian conductance target x| ≤ residual x) :
    ∀ x, |harmonic x - target x| ≤ boundaryError +
      isingFiniteWeightedSpatialResidualPotential G conductance boundary
        hconductance hpositive hhit residual x := by
  let potential := isingFiniteWeightedSpatialResidualPotential
    G conductance boundary hconductance hpositive hhit residual
  let upper : V → Real := fun x ↦ target x + potential x + boundaryError
  let lower : V → Real := fun x ↦ target x - potential x - boundaryError
  have hpotential_nonneg : ∀ x, 0 ≤ potential x :=
    isingFiniteWeightedSpatialResidualPotential_nonneg
      G conductance boundary hconductance hpositive hhit residual
        hresidual_nonneg
  have hupper_super :
      IsingFiniteWeightedSuperharmonicOn conductance boundary upper := by
    intro x hx
    rw [show upper = fun y ↦ (target y + potential y) + boundaryError by rfl,
      isingFiniteWeightedLaplacian_add_const,
      isingFiniteWeightedLaplacian_add]
    have ht := (abs_le.mp (htarget_residual x hx)).2
    have hp := isingFiniteWeightedSpatialResidualPotential_laplacian
      G conductance boundary hconductance hpositive hhit residual x hx
    change isingFiniteWeightedLaplacian conductance potential x =
      -residual x at hp
    linarith
  have hlower_sub :
      IsingFiniteWeightedSubharmonicOn conductance boundary lower := by
    intro x hx
    rw [show lower = fun y ↦
        (target y + (-1) * potential y) + (-boundaryError) by
          funext y
          dsimp only [lower]
          ring,
      isingFiniteWeightedLaplacian_add_const,
      isingFiniteWeightedLaplacian_add,
      isingFiniteWeightedLaplacian_const_mul]
    have ht := (abs_le.mp (htarget_residual x hx)).1
    have hp := isingFiniteWeightedSpatialResidualPotential_laplacian
      G conductance boundary hconductance hpositive hhit residual x hx
    change isingFiniteWeightedLaplacian conductance potential x =
      -residual x at hp
    linarith
  have hupper : ∀ x, harmonic x ≤ upper x := by
    apply isingFiniteWeighted_harmonic_le_superharmonic
      G conductance boundary harmonic upper hconductance hpositive hhit
      hharmonic hupper_super
    intro x hx
    have hb := (abs_le.mp (hboundary x hx)).2
    have hp := isingFiniteWeightedSpatialResidualPotential_boundary
      G conductance boundary hconductance hpositive hhit residual x hx
    change potential x = 0 at hp
    dsimp only [upper]
    linarith
  have hlower : ∀ x, lower x ≤ harmonic x := by
    apply isingFiniteWeighted_subharmonic_le_harmonic
      G conductance boundary lower harmonic hconductance hpositive hhit
      hlower_sub hharmonic
    intro x hx
    have hb := (abs_le.mp (hboundary x hx)).1
    have hp := isingFiniteWeightedSpatialResidualPotential_boundary
      G conductance boundary hconductance hpositive hhit residual x hx
    change potential x = 0 at hp
    dsimp only [lower]
    linarith
  intro x
  rw [abs_le]
  have hup := hupper x
  have hlo := hlower x
  have hp := hpotential_nonneg x
  dsimp only [upper] at hup
  dsimp only [lower] at hlo
  constructor <;> linarith

end
end StatMech.Universality

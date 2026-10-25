/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWeightedDirichletComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDirichletComparison.Part5
import Def.StatisticalMechanics.Code.Universality.IsingFermionicWeightedDirichletComparison.Part5
open Finset SimpleGraph


namespace StatMech.Universality

noncomputable section

theorem isingFiniteWeightedPoissonBarrier_le_bound
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V → V → Real)
    (boundary : V → Prop)
    (hconductance : ∀ x y, 0 ≤ conductance x y)
    (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (x : V) :
    isingFiniteWeightedPoissonBarrier G conductance boundary
        hconductance hpositive hhit x ≤
      isingFiniteWeightedPoissonBarrierBound G conductance boundary
        hconductance hpositive hhit := by
  classical
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩

theorem isingFiniteWeightedPoissonBarrierBound_nonneg
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V → V → Real)
    (boundary : V → Prop)
    (hconductance : ∀ x y, 0 ≤ conductance x y)
    (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b) :
    0 ≤ isingFiniteWeightedPoissonBarrierBound G conductance boundary
      hconductance hpositive hhit := by
  let x : V := Classical.choice inferInstance
  exact (isingFiniteWeightedPoissonBarrier_nonneg G conductance boundary
    hconductance hpositive hhit x).trans
      (isingFiniteWeightedPoissonBarrier_le_bound G conductance boundary
        hconductance hpositive hhit x)


theorem isingFiniteWeighted_harmonic_approximation_of_barrier
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V → V → Real)
    (boundary : V → Prop) (harmonic target barrier : V → Real)
    (boundaryError residual barrierBound : Real)
    (hconductance : ∀ x y, 0 ≤ conductance x y)
    (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (hharmonic : IsingFiniteWeightedHarmonicOn
      conductance boundary harmonic)
    (hboundary : ∀ x, boundary x →
      |harmonic x - target x| ≤ boundaryError)
    (hresidual_nonneg : 0 ≤ residual)
    (hbarrier_nonneg : ∀ x, 0 ≤ barrier x)
    (hbarrier_bound : ∀ x, barrier x ≤ barrierBound)
    (hbarrier_laplacian : ∀ x, ¬ boundary x →
      isingFiniteWeightedLaplacian conductance barrier x ≤ -1)
    (htarget_residual : ∀ x, ¬ boundary x →
      |isingFiniteWeightedLaplacian conductance target x| ≤ residual) :
    ∀ x, |harmonic x - target x| ≤
      boundaryError + residual * barrierBound := by
  let upper : V → Real := fun x ↦
    target x + residual * barrier x + boundaryError
  let lower : V → Real := fun x ↦
    target x + (-residual) * barrier x - boundaryError
  have hupper_super :
      IsingFiniteWeightedSuperharmonicOn conductance boundary upper := by
    intro x hx
    rw [show upper = fun y ↦
        (target y + residual * barrier y) + boundaryError by rfl,
      isingFiniteWeightedLaplacian_add_const,
      isingFiniteWeightedLaplacian_add,
      isingFiniteWeightedLaplacian_const_mul]
    have ht := (abs_le.mp (htarget_residual x hx)).2
    have hb := hbarrier_laplacian x hx
    nlinarith
  have hlower_sub :
      IsingFiniteWeightedSubharmonicOn conductance boundary lower := by
    intro x hx
    rw [show lower = fun y ↦
        (target y + (-residual) * barrier y) + (-boundaryError) by
          funext y
          dsimp only [lower]
          ring,
      isingFiniteWeightedLaplacian_add_const,
      isingFiniteWeightedLaplacian_add,
      isingFiniteWeightedLaplacian_const_mul]
    have ht := (abs_le.mp (htarget_residual x hx)).1
    have hb := hbarrier_laplacian x hx
    nlinarith
  have hupper : ∀ x, harmonic x ≤ upper x := by
    apply isingFiniteWeighted_harmonic_le_superharmonic
      G conductance boundary harmonic upper hconductance hpositive hhit
      hharmonic hupper_super
    intro x hx
    have hb := (abs_le.mp (hboundary x hx)).2
    have hbar := hbarrier_nonneg x
    dsimp only [upper]
    nlinarith
  have hlower : ∀ x, lower x ≤ harmonic x := by
    apply isingFiniteWeighted_subharmonic_le_harmonic
      G conductance boundary lower harmonic hconductance hpositive hhit
      hlower_sub hharmonic
    intro x hx
    have hb := (abs_le.mp (hboundary x hx)).1
    have hbar := hbarrier_nonneg x
    dsimp only [lower]
    nlinarith
  intro x
  rw [abs_le]
  have hbar := hbarrier_bound x
  have hup := hupper x
  have hlo := hlower x
  dsimp only [upper] at hup
  dsimp only [lower] at hlo
  constructor <;> nlinarith


theorem isingFiniteWeighted_harmonic_approximation_of_residual
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V → V → Real)
    (boundary : V → Prop) (harmonic target : V → Real)
    (boundaryError residual : Real)
    (hconductance : ∀ x y, 0 ≤ conductance x y)
    (hpositive : ∀ ⦃x y⦄, G.Adj x y → 0 < conductance x y)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (hharmonic : IsingFiniteWeightedHarmonicOn
      conductance boundary harmonic)
    (hboundary : ∀ x, boundary x →
      |harmonic x - target x| ≤ boundaryError)
    (hresidual_nonneg : 0 ≤ residual)
    (htarget_residual : ∀ x, ¬ boundary x →
      |isingFiniteWeightedLaplacian conductance target x| ≤ residual) :
    ∀ x, |harmonic x - target x| ≤ boundaryError + residual *
      isingFiniteWeightedPoissonBarrierBound G conductance boundary
        hconductance hpositive hhit := by
  apply isingFiniteWeighted_harmonic_approximation_of_barrier
    G conductance boundary harmonic target
    (isingFiniteWeightedPoissonBarrier G conductance boundary
      hconductance hpositive hhit)
    boundaryError residual
    (isingFiniteWeightedPoissonBarrierBound G conductance boundary
      hconductance hpositive hhit)
    hconductance hpositive hhit hharmonic hboundary hresidual_nonneg
    (isingFiniteWeightedPoissonBarrier_nonneg G conductance boundary
      hconductance hpositive hhit)
    (isingFiniteWeightedPoissonBarrier_le_bound G conductance boundary
      hconductance hpositive hhit)
  · intro x hx
    rw [isingFiniteWeightedPoissonBarrier_laplacian
      G conductance boundary hconductance hpositive hhit x hx]
  · exact htarget_residual


end
end StatMech.Universality

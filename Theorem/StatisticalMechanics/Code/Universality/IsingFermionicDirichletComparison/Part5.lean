/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDirichletComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPrimitiveIntegration
import Def.StatisticalMechanics.Code.Universality.IsingFermionicDirichletComparison.Part5
open Finset SimpleGraph


namespace StatMech.Universality

noncomputable section

theorem isingFiniteGraphPoissonBarrier_le_bound
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (boundary : V → Prop)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (x : V) :
    isingFiniteGraphPoissonBarrier G boundary hhit x ≤
      isingFiniteGraphPoissonBarrierBound G boundary hhit := by
  classical
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩


theorem isingFiniteGraph_subsuperharmonic_boundary_stability
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (boundary : V → Prop)
    (u h : V → ℝ) (eps : ℝ)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (husub : IsingFiniteGraphSubharmonicOn G boundary u)
    (husuper : IsingFiniteGraphSuperharmonicOn G boundary u)
    (hh : IsingFiniteGraphHarmonicOn G boundary h)
    (hboundary : ∀ x, boundary x → |u x - h x| ≤ eps) :
    ∀ x, |u x - h x| ≤ eps := by
  have hupper : ∀ x, u x ≤ h x + eps := by
    apply isingFiniteGraph_subharmonic_le_harmonic G boundary u
      (fun x ↦ h x + eps) hhit husub (hh.add_const eps)
    intro x hx
    have hb := hboundary x hx
    rw [abs_le] at hb
    linarith
  have hlower : ∀ x, h x ≤ u x + eps := by
    apply isingFiniteGraph_harmonic_le_superharmonic G boundary h
      (fun x ↦ u x + eps) hhit hh
    · intro x hx
      rw [isingFiniteGraphLaplacian_add_const]
      exact husuper x hx
    · intro x hx
      have hb := hboundary x hx
      rw [abs_le] at hb
      linarith
  intro x
  rw [abs_le]
  constructor <;> linarith [hupper x, hlower x]


theorem isingFiniteGraph_harmonic_approximation_of_barrier
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (boundary : V → Prop)
    (harmonic target barrier : V → ℝ)
    (boundaryError residual barrierBound : ℝ)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (hharmonic : IsingFiniteGraphHarmonicOn G boundary harmonic)
    (hboundary : ∀ x, boundary x →
      |harmonic x - target x| ≤ boundaryError)
    (hresidual_nonneg : 0 ≤ residual)
    (hbarrier_nonneg : ∀ x, 0 ≤ barrier x)
    (hbarrier_bound : ∀ x, barrier x ≤ barrierBound)
    (hbarrier_laplacian : ∀ x, ¬ boundary x →
      isingFiniteGraphLaplacian G barrier x ≤ -1)
    (htarget_residual : ∀ x, ¬ boundary x →
      |isingFiniteGraphLaplacian G target x| ≤ residual) :
    ∀ x, |harmonic x - target x| ≤
      boundaryError + residual * barrierBound := by
  let upper : V → ℝ := fun x ↦
    target x + residual * barrier x + boundaryError
  let lower : V → ℝ := fun x ↦
    target x + (-residual) * barrier x - boundaryError
  have hupper_super :
      IsingFiniteGraphSuperharmonicOn G boundary upper := by
    intro x hx
    rw [show upper = fun y ↦
        (target y + residual * barrier y) + boundaryError by rfl,
      isingFiniteGraphLaplacian_add_const,
      isingFiniteGraphLaplacian_add,
      isingFiniteGraphLaplacian_const_mul]
    have ht := (abs_le.mp (htarget_residual x hx)).2
    have hb := hbarrier_laplacian x hx
    nlinarith
  have hlower_sub :
      IsingFiniteGraphSubharmonicOn G boundary lower := by
    intro x hx
    rw [show lower = fun y ↦
        (target y + (-residual) * barrier y) + (-boundaryError) by
          funext y
          dsimp only [lower]
          ring,
      isingFiniteGraphLaplacian_add_const,
      isingFiniteGraphLaplacian_add,
      isingFiniteGraphLaplacian_const_mul]
    have ht := (abs_le.mp (htarget_residual x hx)).1
    have hb := hbarrier_laplacian x hx
    nlinarith
  have hupper : ∀ x, harmonic x ≤ upper x := by
    apply isingFiniteGraph_harmonic_le_superharmonic
      G boundary harmonic upper hhit hharmonic hupper_super
    intro x hx
    have hb := (abs_le.mp (hboundary x hx)).2
    have hbar := hbarrier_nonneg x
    dsimp only [upper]
    nlinarith
  have hlower : ∀ x, lower x ≤ harmonic x := by
    apply isingFiniteGraph_subharmonic_le_harmonic
      G boundary lower harmonic hhit hlower_sub hharmonic
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


theorem isingFiniteGraph_harmonic_approximation_of_residual
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (boundary : V → Prop)
    (harmonic target : V → ℝ) (boundaryError residual : ℝ)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (hharmonic : IsingFiniteGraphHarmonicOn G boundary harmonic)
    (hboundary : ∀ x, boundary x →
      |harmonic x - target x| ≤ boundaryError)
    (hresidual_nonneg : 0 ≤ residual)
    (htarget_residual : ∀ x, ¬ boundary x →
      |isingFiniteGraphLaplacian G target x| ≤ residual) :
    ∀ x, |harmonic x - target x| ≤ boundaryError + residual *
      isingFiniteGraphPoissonBarrierBound G boundary hhit := by
  apply isingFiniteGraph_harmonic_approximation_of_barrier
    G boundary harmonic target
    (isingFiniteGraphPoissonBarrier G boundary hhit)
    boundaryError residual
    (isingFiniteGraphPoissonBarrierBound G boundary hhit)
    hhit hharmonic hboundary hresidual_nonneg
    (isingFiniteGraphPoissonBarrier_nonneg G boundary hhit)
    (isingFiniteGraphPoissonBarrier_le_bound G boundary hhit)
  · intro x hx
    rw [isingFiniteGraphPoissonBarrier_laplacian G boundary hhit x hx]
  · exact htarget_residual

end
end StatMech.Universality

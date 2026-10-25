/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDirichletComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPrimitiveIntegration
import Def.StatisticalMechanics.Code.Universality.IsingFermionicDirichletComparison.Part4
open Finset SimpleGraph


namespace StatMech.Universality

noncomputable section

theorem isingFiniteGraphPoissonBarrier_boundary
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (boundary : V → Prop)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (x : V) (hx : boundary x) :
    isingFiniteGraphPoissonBarrier G boundary hhit x = 0 := by
  classical
  have h := congrFun
    (isingFiniteGraphDirichletOperator_solve G boundary hhit
      (fun y ↦ if boundary y then 0 else -1)) x
  change (if boundary x then
      isingFiniteGraphPoissonBarrier G boundary hhit x else
      isingFiniteGraphLaplacian G
        (isingFiniteGraphPoissonBarrier G boundary hhit) x) =
    (if boundary x then 0 else -1) at h
  simpa [hx] using h

theorem isingFiniteGraphPoissonBarrier_laplacian
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (boundary : V → Prop)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b)
    (x : V) (hx : ¬ boundary x) :
    isingFiniteGraphLaplacian G
      (isingFiniteGraphPoissonBarrier G boundary hhit) x = -1 := by
  classical
  have h := congrFun
    (isingFiniteGraphDirichletOperator_solve G boundary hhit
      (fun y ↦ if boundary y then 0 else -1)) x
  change (if boundary x then
      isingFiniteGraphPoissonBarrier G boundary hhit x else
      isingFiniteGraphLaplacian G
        (isingFiniteGraphPoissonBarrier G boundary hhit) x) =
    (if boundary x then 0 else -1) at h
  simpa [hx] using h

theorem isingFiniteGraphPoissonBarrier_nonneg
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (boundary : V → Prop)
    (hhit : ∀ x, ∃ b, boundary b ∧ G.Reachable x b) :
    ∀ x, 0 ≤ isingFiniteGraphPoissonBarrier G boundary hhit x := by
  have hzero : IsingFiniteGraphHarmonicOn G boundary (fun _ ↦ 0) := by
    intro x hx
    unfold isingFiniteGraphLaplacian
    simp
  have hsuper : IsingFiniteGraphSuperharmonicOn G boundary
      (isingFiniteGraphPoissonBarrier G boundary hhit) := by
    intro x hx
    rw [isingFiniteGraphPoissonBarrier_laplacian G boundary hhit x hx]
    norm_num
  apply isingFiniteGraph_harmonic_le_superharmonic
    G boundary (fun _ ↦ 0)
    (isingFiniteGraphPoissonBarrier G boundary hhit)
    hhit hzero hsuper
  intro x hx
  rw [isingFiniteGraphPoissonBarrier_boundary G boundary hhit x hx]


end
end StatMech.Universality

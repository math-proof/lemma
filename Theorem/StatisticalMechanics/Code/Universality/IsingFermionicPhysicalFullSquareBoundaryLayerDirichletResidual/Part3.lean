/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletResidual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichlet.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichletResidual.Part3


namespace StatMech.Universality

open Filter Set Topology

open Finset

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem vertexBoundaryConsistencyError_fixed_bound
    (n : Nat) (hn : 0 < n)
    (target : Option (FKIsingSquareFullVertexNode n) → Real)
    (x : FKIsingSquareFullVertexNode n)
    (hx : fkIsingSquareFullVertexFixedBoundary n x) :
    |0 - target (some x)| ≤ vertexBoundaryConsistencyError n hn target := by
  have h := isingFiniteWeightedBoundaryError_bound
    (vertexDirichletBoundary n) (vertexGhostPrimitive n hn) target
    (some x) hx
  simpa [vertexBoundaryConsistencyError, vertexGhostPrimitive,
    isingFiniteGhostExtension, vertex_fixedBoundary_eq_zero n hn x hx] using h

theorem vertexBoundaryConsistencyError_ghost_bound
    (n : Nat) (hn : 0 < n)
    (target : Option (FKIsingSquareFullVertexNode n) → Real) :
    |1 - target none| ≤ vertexBoundaryConsistencyError n hn target := by
  have h := isingFiniteWeightedBoundaryError_bound
    (vertexDirichletBoundary n) (vertexGhostPrimitive n hn) target
    none trivial
  simpa [vertexBoundaryConsistencyError, vertexGhostPrimitive,
    isingFiniteGhostExtension] using h

theorem faceBoundaryConsistencyError_fixed_bound
    (n : Nat) (hn : 0 < n)
    (target : Option (FKIsingSquareFullFaceNode n) → Real)
    (c : FKIsingSquareFullFaceNode n)
    (hc : fkIsingSquareFullFaceFixedBoundary n c) :
    |1 - target (some c)| ≤ faceBoundaryConsistencyError n hn target := by
  have h := isingFiniteWeightedBoundaryError_bound
    (faceDirichletBoundary n) (faceGhostPrimitive n hn) target
    (some c) hc
  simpa [faceBoundaryConsistencyError, faceGhostPrimitive,
    isingFiniteGhostExtension, face_fixedBoundary_eq_one n hn c hc] using h

theorem faceBoundaryConsistencyError_ghost_bound
    (n : Nat) (hn : 0 < n)
    (target : Option (FKIsingSquareFullFaceNode n) → Real) :
    |0 - target none| ≤ faceBoundaryConsistencyError n hn target := by
  have h := isingFiniteWeightedBoundaryError_bound
    (faceDirichletBoundary n) (faceGhostPrimitive n hn) target
    none trivial
  simpa [faceBoundaryConsistencyError, faceGhostPrimitive,
    isingFiniteGhostExtension] using h


theorem vertexTargetResidual_robin_bound
    (n : Nat)
    (target : Option (FKIsingSquareFullVertexNode n) → Real)
    (x : FKIsingSquareFullVertexNode n)
    (hx : ¬ fkIsingSquareFullVertexFixedBoundary n x) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
          (fun y ↦ target (some y)) x +
        isingFermionicGhostRate
          (fkIsingSquareFullVertexGhostMultiplicity n) x *
            (target none - target (some x))| ≤
      vertexTargetResidual n target := by
  have h := isingFiniteWeightedTargetResidual_bound
    (vertexGhostConductance n) (vertexDirichletBoundary n) target
    (some x) hx
  have htarget : target = isingFiniteGhostExtension (target none)
      (fun y ↦ target (some y)) := by
    funext z
    cases z <;> rfl
  have hlap : isingFiniteWeightedLaplacian (vertexGhostConductance n)
      target (some x) =
      isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
          (fun y ↦ target (some y)) x +
        isingFermionicGhostRate
          (fkIsingSquareFullVertexGhostMultiplicity n) x *
            (target none - target (some x)) := by
    calc
      _ = isingFiniteWeightedLaplacian (vertexGhostConductance n)
          (isingFiniteGhostExtension (target none)
            (fun y ↦ target (some y))) (some x) := by rw [← htarget]
      _ = _ := by
        simpa [vertexGhostConductance] using
          isingFiniteGhostLaplacian_some
            (fkIsingSquareFullVertexGraph n)
            (isingFermionicGhostRate
              (fkIsingSquareFullVertexGhostMultiplicity n))
            (target none) (fun y ↦ target (some y)) x
  rw [hlap] at h
  exact h


theorem faceTargetResidual_robin_bound
    (n : Nat)
    (target : Option (FKIsingSquareFullFaceNode n) → Real)
    (c : FKIsingSquareFullFaceNode n)
    (hc : ¬ fkIsingSquareFullFaceFixedBoundary n c) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
          (fun d ↦ target (some d)) c +
        isingFermionicGhostRate
          (fkIsingSquareFullFaceGhostMultiplicity n) c *
            (target none - target (some c))| ≤
      faceTargetResidual n target := by
  have h := isingFiniteWeightedTargetResidual_bound
    (faceGhostConductance n) (faceDirichletBoundary n) target
    (some c) hc
  have htarget : target = isingFiniteGhostExtension (target none)
      (fun d ↦ target (some d)) := by
    funext z
    cases z <;> rfl
  have hlap : isingFiniteWeightedLaplacian (faceGhostConductance n)
      target (some c) =
      isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
          (fun d ↦ target (some d)) c +
        isingFermionicGhostRate
          (fkIsingSquareFullFaceGhostMultiplicity n) c *
            (target none - target (some c)) := by
    calc
      _ = isingFiniteWeightedLaplacian (faceGhostConductance n)
          (isingFiniteGhostExtension (target none)
            (fun d ↦ target (some d))) (some c) := by rw [← htarget]
      _ = _ := by
        simpa [faceGhostConductance] using
          isingFiniteGhostLaplacian_some
            (fkIsingSquareFullFaceGraph n)
            (isingFermionicGhostRate
              (fkIsingSquareFullFaceGhostMultiplicity n))
            (target none) (fun d ↦ target (some d)) c
  rw [hlap] at h
  exact h


theorem vertexDirichlet_target_error_le
    (n : Nat) (hn : 0 < n)
    (target : Option (FKIsingSquareFullVertexNode n) → Real) :
    ∀ x, |vertexDirichlet n hn x - target x| ≤
      vertexTargetConsistencyError n hn target := by
  apply isingFiniteWeighted_harmonic_approximation_of_residual
    (vertexGhostGraph n) (vertexGhostConductance n)
    (vertexDirichletBoundary n) (vertexDirichlet n hn) target
    (vertexBoundaryConsistencyError n hn target)
    (vertexTargetResidual n target)
    (vertexGhostConductance_nonneg n)
    (vertexGhostConductance_pos_of_adj n)
    (vertexGhost_reaches_boundary n) (vertexDirichlet_harmonicOn n hn)
  · intro x hx
    rw [vertexDirichlet_boundary n hn x hx]
    exact isingFiniteWeightedBoundaryError_bound
      (vertexDirichletBoundary n) (vertexGhostPrimitive n hn) target x hx
  · exact isingFiniteWeightedTargetResidual_nonneg
      (vertexGhostConductance n) (vertexDirichletBoundary n) target
  · intro x hx
    exact isingFiniteWeightedTargetResidual_bound
      (vertexGhostConductance n) (vertexDirichletBoundary n) target x hx


theorem faceDirichlet_target_error_le
    (n : Nat) (hn : 0 < n)
    (target : Option (FKIsingSquareFullFaceNode n) → Real) :
    ∀ c, |faceDirichlet n hn c - target c| ≤
      faceTargetConsistencyError n hn target := by
  apply isingFiniteWeighted_harmonic_approximation_of_residual
    (faceGhostGraph n) (faceGhostConductance n)
    (faceDirichletBoundary n) (faceDirichlet n hn) target
    (faceBoundaryConsistencyError n hn target)
    (faceTargetResidual n target)
    (faceGhostConductance_nonneg n)
    (faceGhostConductance_pos_of_adj n)
    (faceGhost_reaches_boundary n) (faceDirichlet_harmonicOn n hn)
  · intro c hc
    rw [faceDirichlet_boundary n hn c hc]
    exact isingFiniteWeightedBoundaryError_bound
      (faceDirichletBoundary n) (faceGhostPrimitive n hn) target c hc
  · exact isingFiniteWeightedTargetResidual_nonneg
      (faceGhostConductance n) (faceDirichletBoundary n) target
  · intro c hc
    exact isingFiniteWeightedTargetResidual_bound
      (faceGhostConductance n) (faceDirichletBoundary n) target c hc


theorem physicalIncidence_target_error_le
    (n : Nat) (hn : 0 < n)
    (vertexTarget : Option (FKIsingSquareFullVertexNode n) → Real)
    (faceTarget : Option (FKIsingSquareFullFaceNode n) → Real)
    (e : FKIsingSquareInteriorRadialIncidence n hn)
    (target : Real)
    (hvertexTarget : vertexTarget
      (some (fkIsingSquareInteriorRadialEndpoint n hn e)) = target)
    (hfaceTarget : faceTarget
      (some (fkIsingSquareFullFaceOfRadialIncidence n hn e)) = target) :
    |(fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
        (fkIsingSquareInteriorRadialEndpoint n hn e) - target| ≤
        max (vertexTargetConsistencyError n hn vertexTarget)
          (faceTargetConsistencyError n hn faceTarget) ∧
      |(fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
        (fkIsingSquareFullFaceOfRadialIncidence n hn e) - target| ≤
        max (vertexTargetConsistencyError n hn vertexTarget)
          (faceTargetConsistencyError n hn faceTarget) := by
  apply physicalIncidence_close_of_dirichlet_close n hn e target
  · rw [← hvertexTarget]
    exact (vertexDirichlet_target_error_le n hn vertexTarget _).trans
      (le_max_left _ _)
  · rw [← hfaceTarget]
    exact (faceDirichlet_target_error_le n hn faceTarget _).trans
      (le_max_right _ _)


theorem physicalIncidence_uniform_convergence_of_weightedConsistency
    (N : Nat → Nat) (hN : ∀ k, 0 < N k)
    (vertexTarget : ∀ k,
      Option (FKIsingSquareFullVertexNode (N k)) → Real)
    (faceTarget : ∀ k,
      Option (FKIsingSquareFullFaceNode (N k)) → Real)
    (incidenceTarget : ∀ k,
      FKIsingSquareInteriorRadialIncidence (N k) (hN k) → Real)
    (hvertexTarget : ∀ k e, vertexTarget k
      (some (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e)) =
        incidenceTarget k e)
    (hfaceTarget : ∀ k e, faceTarget k
      (some (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e)) =
        incidenceTarget k e)
    (hconsistency : Tendsto (fun k ↦
      max (vertexTargetConsistencyError
        (N k) (hN k) (vertexTarget k))
        (faceTargetConsistencyError
          (N k) (hN k) (faceTarget k))) atTop (nhds 0)) :
    ∀ eta : Real, 0 < eta → ∀ᶠ k in atTop,
      ∀ e : FKIsingSquareInteriorRadialIncidence (N k) (hN k),
        |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (N k) (hN k)).vertexPrimitive
            (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e) -
              incidenceTarget k e| < eta ∧
          |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (N k) (hN k)).facePrimitive
            (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e) -
              incidenceTarget k e| < eta := by
  intro eta heta
  have hevent : ∀ᶠ k in atTop,
      max (vertexTargetConsistencyError
        (N k) (hN k) (vertexTarget k))
        (faceTargetConsistencyError
          (N k) (hN k) (faceTarget k)) < eta :=
    hconsistency (Iio_mem_nhds heta)
  filter_upwards [hevent] with k hk
  intro e
  have h := physicalIncidence_target_error_le
    (N k) (hN k) (vertexTarget k) (faceTarget k) e
    (incidenceTarget k e) (hvertexTarget k e) (hfaceTarget k e)
  exact ⟨lt_of_le_of_lt h.1 hk, lt_of_le_of_lt h.2 hk⟩

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality

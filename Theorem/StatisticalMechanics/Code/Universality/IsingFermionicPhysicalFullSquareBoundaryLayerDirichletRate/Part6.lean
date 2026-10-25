/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichletResidual.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryApproximation.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareGridConsistency.Part4
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.Part6


namespace StatMech.Universality

open Filter Finset Set Topology

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem vertexBarrierGrowthConstant_nonneg :
    0 ≤ vertexBarrierGrowthConstant := by
  unfold vertexBarrierGrowthConstant
  exact add_nonneg (by norm_num)
    (div_nonneg (by norm_num) isingFermionicGhostCoefficient_pos.le)

theorem half_le_vertexBarrierGrowthConstant :
    (1 / 2 : Real) ≤ vertexBarrierGrowthConstant := by
  unfold vertexBarrierGrowthConstant
  have h : 0 ≤ 3 / isingFermionicGhostCoefficient :=
    div_nonneg (by norm_num) isingFermionicGhostCoefficient_pos.le
  linarith

theorem vertexExplicitPoissonBarrierBound_le_growth
    (n : Nat) (hn : 0 < n) :
    vertexExplicitPoissonBarrierBound n ≤
      vertexBarrierGrowthConstant * (n : Real) ^ 2 := by
  have hn1 : (1 : Real) ≤ (n : Real) := by exact_mod_cast hn
  have hsquare : (1 : Real) ≤ (n : Real) ^ 2 := by nlinarith
  have hnum : 2 * (n : Real) ^ 2 + 1 ≤ 3 * (n : Real) ^ 2 := by
    linarith
  unfold vertexExplicitPoissonBarrierBound vertexBarrierOffset
    vertexBarrierGrowthConstant
  calc
    (n : Real) ^ 2 / 2 +
        (2 * (n : Real) ^ 2 + 1) / isingFermionicGhostCoefficient ≤
      (n : Real) ^ 2 / 2 +
        (3 * (n : Real) ^ 2) / isingFermionicGhostCoefficient := by
      simpa [add_comm] using
        (add_le_add_left
          (div_le_div_of_nonneg_right hnum
            isingFermionicGhostCoefficient_pos.le)
          ((n : Real) ^ 2 / 2))
    _ = (1 / 2 + 3 / isingFermionicGhostCoefficient) *
        (n : Real) ^ 2 := by ring

theorem vertexPoissonBarrierBound_le_growth
    (n : Nat) (hn : 0 < n) :
    vertexPoissonBarrierBound n ≤
      vertexBarrierGrowthConstant * (n : Real) ^ 2 :=
  (vertexPoissonBarrierBound_le_explicit n hn).trans
    (vertexExplicitPoissonBarrierBound_le_growth n hn)

theorem facePoissonBarrierBound_le_growth (n : Nat) :
    facePoissonBarrierBound n ≤
      vertexBarrierGrowthConstant * (n : Real) ^ 2 := by
  calc
    facePoissonBarrierBound n ≤ faceExplicitPoissonBarrierBound n :=
      facePoissonBarrierBound_le_explicit n
    _ = (1 / 2 : Real) * (n : Real) ^ 2 := by
      unfold faceExplicitPoissonBarrierBound
      ring
    _ ≤ vertexBarrierGrowthConstant * (n : Real) ^ 2 :=
      mul_le_mul_of_nonneg_right half_le_vertexBarrierGrowthConstant
        (sq_nonneg _)

theorem vertexTargetConsistencyError_nonneg
    (n : Nat) (hn : 0 < n)
    (target : Option (FKIsingSquareFullVertexNode n) → Real) :
    0 ≤ vertexTargetConsistencyError n hn target := by
  unfold vertexTargetConsistencyError
  exact add_nonneg
    (isingFiniteWeightedBoundaryError_nonneg
      (vertexDirichletBoundary n) (vertexGhostPrimitive n hn) target)
    (mul_nonneg
      (isingFiniteWeightedTargetResidual_nonneg
        (vertexGhostConductance n) (vertexDirichletBoundary n) target)
      (isingFiniteWeightedPoissonBarrierBound_nonneg
        (vertexGhostGraph n) (vertexGhostConductance n)
        (vertexDirichletBoundary n) (vertexGhostConductance_nonneg n)
        (vertexGhostConductance_pos_of_adj n)
        (vertexGhost_reaches_boundary n)))

theorem faceTargetConsistencyError_nonneg
    (n : Nat) (hn : 0 < n)
    (target : Option (FKIsingSquareFullFaceNode n) → Real) :
    0 ≤ faceTargetConsistencyError n hn target := by
  unfold faceTargetConsistencyError
  exact add_nonneg
    (isingFiniteWeightedBoundaryError_nonneg
      (faceDirichletBoundary n) (faceGhostPrimitive n hn) target)
    (mul_nonneg
      (isingFiniteWeightedTargetResidual_nonneg
        (faceGhostConductance n) (faceDirichletBoundary n) target)
      (isingFiniteWeightedPoissonBarrierBound_nonneg
        (faceGhostGraph n) (faceGhostConductance n)
        (faceDirichletBoundary n) (faceGhostConductance_nonneg n)
        (faceGhostConductance_pos_of_adj n)
        (faceGhost_reaches_boundary n)))


theorem sampledWeightedConsistency_tendsto_of_quadraticRates
    (N : Nat → Nat) (hN : ∀ k, 0 < N k)
    (vertexEmbedding : ∀ k,
      FKIsingSquareFullVertexNode (N k) → Complex)
    (faceEmbedding : ∀ k,
      FKIsingSquareFullFaceNode (N k) → Complex)
    (Phi : Complex → Complex)
    (boundaryRate residualRate : Nat → Real)
    (hboundary_nonneg : ∀ k, 0 ≤ boundaryRate k)
    (hresidual_nonneg : ∀ k, 0 ≤ residualRate k)
    (hvertexFixed : ∀ k x,
      fkIsingSquareFullVertexFixedBoundary (N k) x →
        |0 - (Phi (vertexEmbedding k x)).im| ≤ boundaryRate k)
    (hfaceFixed : ∀ k c,
      fkIsingSquareFullFaceFixedBoundary (N k) c →
        |1 - (Phi (faceEmbedding k c)).im| ≤ boundaryRate k)
    (hvertexRobin : ∀ k x,
      ¬ fkIsingSquareFullVertexFixedBoundary (N k) x →
        |isingFiniteGraphLaplacian
            (fkIsingSquareFullVertexGraph (N k))
            (fun y ↦ (Phi (vertexEmbedding k y)).im) x +
          isingFermionicGhostRate
              (fkIsingSquareFullVertexGhostMultiplicity (N k)) x *
            (1 - (Phi (vertexEmbedding k x)).im)| ≤ residualRate k)
    (hfaceRobin : ∀ k c,
      ¬ fkIsingSquareFullFaceFixedBoundary (N k) c →
        |isingFiniteGraphLaplacian
            (fkIsingSquareFullFaceGraph (N k))
            (fun d ↦ (Phi (faceEmbedding k d)).im) c +
          isingFermionicGhostRate
              (fkIsingSquareFullFaceGhostMultiplicity (N k)) c *
            (0 - (Phi (faceEmbedding k c)).im)| ≤ residualRate k)
    (hboundary_tendsto : Tendsto boundaryRate atTop (nhds 0))
    (hscaledResidual_tendsto : Tendsto
      (fun k ↦ residualRate k * (N k : Real) ^ 2) atTop (nhds 0)) :
    Tendsto (fun k ↦
      max
        (vertexTargetConsistencyError (N k) (hN k)
          (vertexSampledImaginaryTarget (N k) (vertexEmbedding k) Phi))
        (faceTargetConsistencyError (N k) (hN k)
          (faceSampledImaginaryTarget (N k) (faceEmbedding k) Phi)))
      atTop (nhds 0) := by
  let upper : Nat → Real := fun k ↦
    boundaryRate k + vertexBarrierGrowthConstant *
      (residualRate k * (N k : Real) ^ 2)
  have hvertex (k : Nat) :
      vertexTargetConsistencyError (N k) (hN k)
          (vertexSampledImaginaryTarget (N k) (vertexEmbedding k) Phi) ≤
        upper k := by
    unfold vertexTargetConsistencyError upper
    calc
      vertexBoundaryConsistencyError (N k) (hN k)
            (vertexSampledImaginaryTarget (N k) (vertexEmbedding k) Phi) +
          vertexTargetResidual (N k)
              (vertexSampledImaginaryTarget (N k) (vertexEmbedding k) Phi) *
            vertexPoissonBarrierBound (N k) ≤
        boundaryRate k + residualRate k *
            (vertexBarrierGrowthConstant * (N k : Real) ^ 2) := by
          apply add_le_add
          · exact vertexSampled_boundaryConsistencyError_le
              (N k) (hN k) (vertexEmbedding k) Phi (boundaryRate k)
              (hboundary_nonneg k) (hvertexFixed k)
          · exact mul_le_mul
              (vertexSampled_targetResidual_le
                (N k) (vertexEmbedding k) Phi (residualRate k)
                (hresidual_nonneg k) (hvertexRobin k))
              (vertexPoissonBarrierBound_le_growth (N k) (hN k))
              (isingFiniteWeightedPoissonBarrierBound_nonneg
                (vertexGhostGraph (N k)) (vertexGhostConductance (N k))
                (vertexDirichletBoundary (N k))
                (vertexGhostConductance_nonneg (N k))
                (vertexGhostConductance_pos_of_adj (N k))
                (vertexGhost_reaches_boundary (N k)))
              (hresidual_nonneg k)
      _ = boundaryRate k + vertexBarrierGrowthConstant *
          (residualRate k * (N k : Real) ^ 2) := by ring
  have hface (k : Nat) :
      faceTargetConsistencyError (N k) (hN k)
          (faceSampledImaginaryTarget (N k) (faceEmbedding k) Phi) ≤
        upper k := by
    unfold faceTargetConsistencyError upper
    calc
      faceBoundaryConsistencyError (N k) (hN k)
            (faceSampledImaginaryTarget (N k) (faceEmbedding k) Phi) +
          faceTargetResidual (N k)
              (faceSampledImaginaryTarget (N k) (faceEmbedding k) Phi) *
            facePoissonBarrierBound (N k) ≤
        boundaryRate k + residualRate k *
            (vertexBarrierGrowthConstant * (N k : Real) ^ 2) := by
          apply add_le_add
          · exact faceSampled_boundaryConsistencyError_le
              (N k) (hN k) (faceEmbedding k) Phi (boundaryRate k)
              (hboundary_nonneg k) (hfaceFixed k)
          · exact mul_le_mul
              (faceSampled_targetResidual_le
                (N k) (faceEmbedding k) Phi (residualRate k)
                (hresidual_nonneg k) (hfaceRobin k))
              (facePoissonBarrierBound_le_growth (N k))
              (isingFiniteWeightedPoissonBarrierBound_nonneg
                (faceGhostGraph (N k)) (faceGhostConductance (N k))
                (faceDirichletBoundary (N k))
                (faceGhostConductance_nonneg (N k))
                (faceGhostConductance_pos_of_adj (N k))
                (faceGhost_reaches_boundary (N k)))
              (hresidual_nonneg k)
      _ = boundaryRate k + vertexBarrierGrowthConstant *
          (residualRate k * (N k : Real) ^ 2) := by ring
  have hnonneg (k : Nat) : 0 ≤
      max
        (vertexTargetConsistencyError (N k) (hN k)
          (vertexSampledImaginaryTarget (N k) (vertexEmbedding k) Phi))
        (faceTargetConsistencyError (N k) (hN k)
          (faceSampledImaginaryTarget (N k) (faceEmbedding k) Phi)) :=
    (vertexTargetConsistencyError_nonneg (N k) (hN k)
      (vertexSampledImaginaryTarget (N k) (vertexEmbedding k) Phi)).trans
        (le_max_left _ _)
  have hupper (k : Nat) :
      max
        (vertexTargetConsistencyError (N k) (hN k)
          (vertexSampledImaginaryTarget (N k) (vertexEmbedding k) Phi))
        (faceTargetConsistencyError (N k) (hN k)
          (faceSampledImaginaryTarget (N k) (faceEmbedding k) Phi)) ≤
      upper k := max_le (hvertex k) (hface k)
  have hupper_tendsto : Tendsto upper atTop (nhds 0) := by
    have hscaled : Tendsto (fun k ↦ vertexBarrierGrowthConstant *
        (residualRate k * (N k : Real) ^ 2)) atTop (nhds 0) := by
      simpa using
        (tendsto_const_nhds.mul hscaledResidual_tendsto)
    simpa [upper] using hboundary_tendsto.add hscaled
  exact squeeze_zero hnonneg hupper hupper_tendsto


theorem sampledWeightedConsistency_tendsto_of_meshAndQuadraticResidual
    (N : Nat → Nat) (hN : ∀ k, 0 < N k)
    (vertexEmbedding : ∀ k,
      FKIsingSquareFullVertexNode (N k) → Complex)
    (faceEmbedding : ∀ k,
      FKIsingSquareFullFaceNode (N k) → Complex)
    (Phi : Complex → Complex)
    (mesh residualRate : Nat → Real) (L : Real)
    (hmesh_nonneg : ∀ k, 0 ≤ mesh k) (hL : 0 ≤ L)
    (hresidual_nonneg : ∀ k, 0 ≤ residualRate k)
    (hvertexFixed : ∀ k x,
      fkIsingSquareFullVertexFixedBoundary (N k) x →
        |0 - (Phi (vertexEmbedding k x)).im| ≤ L * mesh k)
    (hfaceFixed : ∀ k c,
      fkIsingSquareFullFaceFixedBoundary (N k) c →
        |1 - (Phi (faceEmbedding k c)).im| ≤ L * mesh k)
    (hvertexRobin : ∀ k x,
      ¬ fkIsingSquareFullVertexFixedBoundary (N k) x →
        |isingFiniteGraphLaplacian
            (fkIsingSquareFullVertexGraph (N k))
            (fun y ↦ (Phi (vertexEmbedding k y)).im) x +
          isingFermionicGhostRate
              (fkIsingSquareFullVertexGhostMultiplicity (N k)) x *
            (1 - (Phi (vertexEmbedding k x)).im)| ≤ residualRate k)
    (hfaceRobin : ∀ k c,
      ¬ fkIsingSquareFullFaceFixedBoundary (N k) c →
        |isingFiniteGraphLaplacian
            (fkIsingSquareFullFaceGraph (N k))
            (fun d ↦ (Phi (faceEmbedding k d)).im) c +
          isingFermionicGhostRate
              (fkIsingSquareFullFaceGhostMultiplicity (N k)) c *
            (0 - (Phi (faceEmbedding k c)).im)| ≤ residualRate k)
    (hmesh_tendsto : Tendsto mesh atTop (nhds 0))
    (hscaledResidual_tendsto : Tendsto
      (fun k ↦ residualRate k * (N k : Real) ^ 2) atTop (nhds 0)) :
    Tendsto (fun k ↦
      max
        (vertexTargetConsistencyError (N k) (hN k)
          (vertexSampledImaginaryTarget (N k) (vertexEmbedding k) Phi))
        (faceTargetConsistencyError (N k) (hN k)
          (faceSampledImaginaryTarget (N k) (faceEmbedding k) Phi)))
      atTop (nhds 0) := by
  apply sampledWeightedConsistency_tendsto_of_quadraticRates
    N hN vertexEmbedding faceEmbedding Phi (fun k ↦ L * mesh k)
      residualRate
  · intro k
    exact mul_nonneg hL (hmesh_nonneg k)
  · exact hresidual_nonneg
  · exact hvertexFixed
  · exact hfaceFixed
  · exact hvertexRobin
  · exact hfaceRobin
  · simpa using tendsto_const_nhds.mul hmesh_tendsto
  · exact hscaledResidual_tendsto


theorem physicalIncidence_sampledTarget_error_le
    (n : Nat) (hn : 0 < n)
    (vertexEmbedding : FKIsingSquareFullVertexNode n → Complex)
    (faceEmbedding : FKIsingSquareFullFaceNode n → Complex)
    (Phi : Complex → Complex)
    (e : FKIsingSquareInteriorRadialIncidence n hn) (target : Real) :
    |(fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
          (fkIsingSquareInteriorRadialEndpoint n hn e) - target| ≤
        max
          (vertexTargetConsistencyError n hn
            (vertexSampledImaginaryTarget n vertexEmbedding Phi))
          (faceTargetConsistencyError n hn
            (faceSampledImaginaryTarget n faceEmbedding Phi)) +
          max
            |(Phi (vertexEmbedding
              (fkIsingSquareInteriorRadialEndpoint n hn e))).im - target|
            |(Phi (faceEmbedding
              (fkIsingSquareFullFaceOfRadialIncidence n hn e))).im - target| ∧
      |(fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (fkIsingSquareFullFaceOfRadialIncidence n hn e) - target| ≤
        max
          (vertexTargetConsistencyError n hn
            (vertexSampledImaginaryTarget n vertexEmbedding Phi))
          (faceTargetConsistencyError n hn
            (faceSampledImaginaryTarget n faceEmbedding Phi)) +
          max
            |(Phi (vertexEmbedding
              (fkIsingSquareInteriorRadialEndpoint n hn e))).im - target|
            |(Phi (faceEmbedding
              (fkIsingSquareFullFaceOfRadialIncidence n hn e))).im - target| := by
  let vertexValue : Real := (Phi (vertexEmbedding
    (fkIsingSquareInteriorRadialEndpoint n hn e))).im
  let faceValue : Real := (Phi (faceEmbedding
    (fkIsingSquareFullFaceOfRadialIncidence n hn e))).im
  let consistency : Real := max
    (vertexTargetConsistencyError n hn
      (vertexSampledImaginaryTarget n vertexEmbedding Phi))
    (faceTargetConsistencyError n hn
      (faceSampledImaginaryTarget n faceEmbedding Phi))
  let mismatch : Real := max |vertexValue - target| |faceValue - target|
  have hvertexSample :
      |vertexDirichlet n hn
          (some (fkIsingSquareInteriorRadialEndpoint n hn e)) - vertexValue| ≤
        vertexTargetConsistencyError n hn
          (vertexSampledImaginaryTarget n vertexEmbedding Phi) := by
    simpa [vertexValue, vertexSampledImaginaryTarget] using
      (vertexDirichlet_target_error_le n hn
        (vertexSampledImaginaryTarget n vertexEmbedding Phi)
        (some (fkIsingSquareInteriorRadialEndpoint n hn e)))
  have hfaceSample :
      |faceDirichlet n hn
          (some (fkIsingSquareFullFaceOfRadialIncidence n hn e)) - faceValue| ≤
        faceTargetConsistencyError n hn
          (faceSampledImaginaryTarget n faceEmbedding Phi) := by
    simpa [faceValue, faceSampledImaginaryTarget] using
      (faceDirichlet_target_error_le n hn
        (faceSampledImaginaryTarget n faceEmbedding Phi)
        (some (fkIsingSquareFullFaceOfRadialIncidence n hn e)))
  have hvertexTarget :
      |vertexDirichlet n hn
          (some (fkIsingSquareInteriorRadialEndpoint n hn e)) - target| ≤
        consistency + mismatch := by
    calc
      |vertexDirichlet n hn
          (some (fkIsingSquareInteriorRadialEndpoint n hn e)) - target| =
        |(vertexDirichlet n hn
            (some (fkIsingSquareInteriorRadialEndpoint n hn e)) -
              vertexValue) + (vertexValue - target)| := by ring_nf
      _ ≤ |vertexDirichlet n hn
              (some (fkIsingSquareInteriorRadialEndpoint n hn e)) -
            vertexValue| + |vertexValue - target| := abs_add_le _ _
      _ ≤ consistency + mismatch := add_le_add
        (hvertexSample.trans (le_max_left _ _)) (le_max_left _ _)
  have hfaceTarget :
      |faceDirichlet n hn
          (some (fkIsingSquareFullFaceOfRadialIncidence n hn e)) - target| ≤
        consistency + mismatch := by
    calc
      |faceDirichlet n hn
          (some (fkIsingSquareFullFaceOfRadialIncidence n hn e)) - target| =
        |(faceDirichlet n hn
            (some (fkIsingSquareFullFaceOfRadialIncidence n hn e)) -
              faceValue) + (faceValue - target)| := by ring_nf
      _ ≤ |faceDirichlet n hn
              (some (fkIsingSquareFullFaceOfRadialIncidence n hn e)) -
            faceValue| + |faceValue - target| := abs_add_le _ _
      _ ≤ consistency + mismatch := add_le_add
        (hfaceSample.trans (le_max_right _ _)) (le_max_right _ _)
  simpa [consistency, mismatch, vertexValue, faceValue] using
    (physicalIncidence_close_of_dirichlet_close n hn e target
      (consistency + mismatch) hvertexTarget hfaceTarget)


theorem physicalIncidence_uniform_convergence_of_sampledConsistency
    (N : Nat → Nat) (hN : ∀ k, 0 < N k)
    (vertexEmbedding : ∀ k,
      FKIsingSquareFullVertexNode (N k) → Complex)
    (faceEmbedding : ∀ k,
      FKIsingSquareFullFaceNode (N k) → Complex)
    (Phi : Complex → Complex)
    (incidenceTarget : ∀ k,
      FKIsingSquareInteriorRadialIncidence (N k) (hN k) → Real)
    (vertexMismatch faceMismatch : Nat → Real)
    (hvertexMismatch : ∀ k e,
      |(Phi (vertexEmbedding k
        (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e))).im -
          incidenceTarget k e| ≤ vertexMismatch k)
    (hfaceMismatch : ∀ k e,
      |(Phi (faceEmbedding k
        (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e))).im -
          incidenceTarget k e| ≤ faceMismatch k)
    (hconsistency : Tendsto (fun k ↦
      max
        (vertexTargetConsistencyError (N k) (hN k)
          (vertexSampledImaginaryTarget (N k) (vertexEmbedding k) Phi))
        (faceTargetConsistencyError (N k) (hN k)
          (faceSampledImaginaryTarget (N k) (faceEmbedding k) Phi)))
      atTop (nhds 0))
    (hvertexMismatch_tendsto : Tendsto vertexMismatch atTop (nhds 0))
    (hfaceMismatch_tendsto : Tendsto faceMismatch atTop (nhds 0)) :
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
  have hmismatch : Tendsto (fun k ↦
      max (vertexMismatch k) (faceMismatch k)) atTop (nhds 0) := by
    simpa using hvertexMismatch_tendsto.max hfaceMismatch_tendsto
  have htotal : Tendsto (fun k ↦
      max
        (vertexTargetConsistencyError (N k) (hN k)
          (vertexSampledImaginaryTarget (N k) (vertexEmbedding k) Phi))
        (faceTargetConsistencyError (N k) (hN k)
          (faceSampledImaginaryTarget (N k) (faceEmbedding k) Phi)) +
        max (vertexMismatch k) (faceMismatch k)) atTop (nhds 0) := by
    simpa using hconsistency.add hmismatch
  have hevent := htotal (Iio_mem_nhds heta)
  filter_upwards [hevent] with k hk
  intro e
  have h := physicalIncidence_sampledTarget_error_le
    (N k) (hN k) (vertexEmbedding k) (faceEmbedding k) Phi e
    (incidenceTarget k e)
  have hmismatchBound :
      max
          |(Phi (vertexEmbedding k
            (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e))).im -
              incidenceTarget k e|
          |(Phi (faceEmbedding k
            (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e))).im -
              incidenceTarget k e| ≤
        max (vertexMismatch k) (faceMismatch k) :=
    max_le
      ((hvertexMismatch k e).trans (le_max_left _ _))
      ((hfaceMismatch k e).trans (le_max_right _ _))
  constructor
  · refine lt_of_le_of_lt (h.1.trans ?_) hk
    exact add_le_add (le_refl _) hmismatchBound
  · refine lt_of_le_of_lt (h.2.trans ?_) hk
    exact add_le_add (le_refl _) hmismatchBound


theorem physicalIncidence_uniform_convergence_of_lipschitzSamples
    (N : Nat → Nat) (hN : ∀ k, 0 < N k)
    (vertexEmbedding : ∀ k,
      FKIsingSquareFullVertexNode (N k) → Complex)
    (faceEmbedding : ∀ k,
      FKIsingSquareFullFaceNode (N k) → Complex)
    (Phi : Complex → Complex) (lipschitzConstant : NNReal)
    (hPhi : LipschitzWith lipschitzConstant (fun z ↦ (Phi z).im))
    (mesh : Nat → Real)
    (embeddingCompatibility : FullSquareCoordinateEmbeddingCompatibility
      N vertexEmbedding faceEmbedding mesh)
    (hconsistency : Tendsto (fun k ↦
      max
        (vertexTargetConsistencyError (N k) (hN k)
          (vertexSampledImaginaryTarget (N k) (vertexEmbedding k) Phi))
        (faceTargetConsistencyError (N k) (hN k)
          (faceSampledImaginaryTarget (N k) (faceEmbedding k) Phi)))
      atTop (nhds 0))
    (hmesh_tendsto : Tendsto mesh atTop (nhds 0)) :
    ∀ eta : Real, 0 < eta → ∀ᶠ k in atTop,
      ∀ e : FKIsingSquareInteriorRadialIncidence (N k) (hN k),
        |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (N k) (hN k)).vertexPrimitive
            (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e) -
              (Phi (vertexEmbedding k
                (fkIsingSquareInteriorRadialEndpoint
                  (N k) (hN k) e))).im| < eta ∧
          |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (N k) (hN k)).facePrimitive
            (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e) -
              (Phi (vertexEmbedding k
                (fkIsingSquareInteriorRadialEndpoint
                  (N k) (hN k) e))).im| < eta := by
  apply physicalIncidence_uniform_convergence_of_sampledConsistency
    N hN vertexEmbedding faceEmbedding Phi
    (fun k e ↦ (Phi (vertexEmbedding k
      (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e))).im)
    (fun _ ↦ 0) (fun k ↦ (lipschitzConstant : Real) * mesh k)
  · intro k e
    simp
  · intro k e
    rw [← Real.dist_eq]
    calc
      dist
          (Phi (faceEmbedding k
            (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e))).im
          (Phi (vertexEmbedding k
            (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e))).im ≤
        lipschitzConstant *
          dist
            (faceEmbedding k
              (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e))
            (vertexEmbedding k
              (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e)) :=
        hPhi.dist_le_mul _ _
      _ ≤ lipschitzConstant * mesh k :=
        mul_le_mul_of_nonneg_left
          (embeddingCompatibility.incidenceDistance (hN := hN) k e)
          lipschitzConstant.2
  · exact hconsistency
  · exact tendsto_const_nhds
  · simpa using tendsto_const_nhds.mul hmesh_tendsto


theorem physicalIncidence_uniform_convergence_of_meshAndQuadraticResidual
    (N : Nat → Nat) (hN : ∀ k, 0 < N k)
    (vertexEmbedding : ∀ k,
      FKIsingSquareFullVertexNode (N k) → Complex)
    (faceEmbedding : ∀ k,
      FKIsingSquareFullFaceNode (N k) → Complex)
    (Phi : Complex → Complex)
    (mesh residualRate : Nat → Real) (boundaryL : Real)
    (lipschitzConstant : NNReal)
    (hmesh_nonneg : ∀ k, 0 ≤ mesh k) (hboundaryL : 0 ≤ boundaryL)
    (hresidual_nonneg : ∀ k, 0 ≤ residualRate k)
    (hvertexFixed : ∀ k x,
      fkIsingSquareFullVertexFixedBoundary (N k) x →
        |0 - (Phi (vertexEmbedding k x)).im| ≤ boundaryL * mesh k)
    (hfaceFixed : ∀ k c,
      fkIsingSquareFullFaceFixedBoundary (N k) c →
        |1 - (Phi (faceEmbedding k c)).im| ≤ boundaryL * mesh k)
    (hvertexRobin : ∀ k x,
      ¬ fkIsingSquareFullVertexFixedBoundary (N k) x →
        |isingFiniteGraphLaplacian
            (fkIsingSquareFullVertexGraph (N k))
            (fun y ↦ (Phi (vertexEmbedding k y)).im) x +
          isingFermionicGhostRate
              (fkIsingSquareFullVertexGhostMultiplicity (N k)) x *
            (1 - (Phi (vertexEmbedding k x)).im)| ≤ residualRate k)
    (hfaceRobin : ∀ k c,
      ¬ fkIsingSquareFullFaceFixedBoundary (N k) c →
        |isingFiniteGraphLaplacian
            (fkIsingSquareFullFaceGraph (N k))
            (fun d ↦ (Phi (faceEmbedding k d)).im) c +
          isingFermionicGhostRate
              (fkIsingSquareFullFaceGhostMultiplicity (N k)) c *
            (0 - (Phi (faceEmbedding k c)).im)| ≤ residualRate k)
    (hPhi : LipschitzWith lipschitzConstant (fun z ↦ (Phi z).im))
    (embeddingCompatibility : FullSquareCoordinateEmbeddingCompatibility
      N vertexEmbedding faceEmbedding mesh)
    (hmesh_tendsto : Tendsto mesh atTop (nhds 0))
    (hscaledResidual_tendsto : Tendsto
      (fun k ↦ residualRate k * (N k : Real) ^ 2) atTop (nhds 0)) :
    ∀ eta : Real, 0 < eta → ∀ᶠ k in atTop,
      ∀ e : FKIsingSquareInteriorRadialIncidence (N k) (hN k),
        |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (N k) (hN k)).vertexPrimitive
            (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e) -
              (Phi (vertexEmbedding k
                (fkIsingSquareInteriorRadialEndpoint
                  (N k) (hN k) e))).im| < eta ∧
          |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (N k) (hN k)).facePrimitive
            (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e) -
              (Phi (vertexEmbedding k
                (fkIsingSquareInteriorRadialEndpoint
                  (N k) (hN k) e))).im| < eta := by
  apply physicalIncidence_uniform_convergence_of_lipschitzSamples
    N hN vertexEmbedding faceEmbedding Phi lipschitzConstant hPhi mesh
      embeddingCompatibility
  · exact sampledWeightedConsistency_tendsto_of_meshAndQuadraticResidual
      N hN vertexEmbedding faceEmbedding Phi mesh residualRate boundaryL
      hmesh_nonneg hboundaryL hresidual_nonneg hvertexFixed hfaceFixed
      hvertexRobin hfaceRobin hmesh_tendsto hscaledResidual_tendsto
  · exact hmesh_tendsto


theorem physicalIncidence_uniform_convergence_of_scaledMeshAndQuadraticResidual
    (N : Nat → Nat) (hN : ∀ k, 0 < N k)
    (Phi : Complex → Complex)
    (mesh residualRate : Nat → Real) (boundaryL : Real)
    (lipschitzConstant : NNReal)
    (hmesh_nonneg : ∀ k, 0 ≤ mesh k) (hboundaryL : 0 ≤ boundaryL)
    (hresidual_nonneg : ∀ k, 0 ≤ residualRate k)
    (hvertexFixed : ∀ k x,
      fkIsingSquareFullVertexFixedBoundary (N k) x →
        |0 - (Phi (fullSquareScaledVertexEmbedding
          (N k) (mesh k) x)).im| ≤ boundaryL * mesh k)
    (hfaceFixed : ∀ k c,
      fkIsingSquareFullFaceFixedBoundary (N k) c →
        |1 - (Phi (fullSquareScaledFaceEmbedding
          (N k) (mesh k) c)).im| ≤ boundaryL * mesh k)
    (hvertexRobin : ∀ k x,
      ¬ fkIsingSquareFullVertexFixedBoundary (N k) x →
        |isingFiniteGraphLaplacian
            (fkIsingSquareFullVertexGraph (N k))
            (fun y ↦ (Phi (fullSquareScaledVertexEmbedding
              (N k) (mesh k) y)).im) x +
          isingFermionicGhostRate
              (fkIsingSquareFullVertexGhostMultiplicity (N k)) x *
            (1 - (Phi (fullSquareScaledVertexEmbedding
              (N k) (mesh k) x)).im)| ≤ residualRate k)
    (hfaceRobin : ∀ k c,
      ¬ fkIsingSquareFullFaceFixedBoundary (N k) c →
        |isingFiniteGraphLaplacian
            (fkIsingSquareFullFaceGraph (N k))
            (fun d ↦ (Phi (fullSquareScaledFaceEmbedding
              (N k) (mesh k) d)).im) c +
          isingFermionicGhostRate
              (fkIsingSquareFullFaceGhostMultiplicity (N k)) c *
            (0 - (Phi (fullSquareScaledFaceEmbedding
              (N k) (mesh k) c)).im)| ≤ residualRate k)
    (hPhi : LipschitzWith lipschitzConstant (fun z ↦ (Phi z).im))
    (hmesh_tendsto : Tendsto mesh atTop (nhds 0))
    (hscaledResidual_tendsto : Tendsto
      (fun k ↦ residualRate k * (N k : Real) ^ 2) atTop (nhds 0)) :
    ∀ eta : Real, 0 < eta → ∀ᶠ k in atTop,
      ∀ e : FKIsingSquareInteriorRadialIncidence (N k) (hN k),
        |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (N k) (hN k)).vertexPrimitive
            (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e) -
              (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k)
                (fkIsingSquareInteriorRadialEndpoint
                  (N k) (hN k) e))).im| < eta ∧
          |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (N k) (hN k)).facePrimitive
            (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e) -
              (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k)
                (fkIsingSquareInteriorRadialEndpoint
                  (N k) (hN k) e))).im| < eta := by
  exact physicalIncidence_uniform_convergence_of_meshAndQuadraticResidual
    N hN
    (fun k ↦ fullSquareScaledVertexEmbedding (N k) (mesh k))
    (fun k ↦ fullSquareScaledFaceEmbedding (N k) (mesh k))
    Phi mesh residualRate boundaryL lipschitzConstant hmesh_nonneg
    hboundaryL hresidual_nonneg hvertexFixed hfaceFixed hvertexRobin
    hfaceRobin hPhi (fullSquareScaledEmbeddingCompatibility N mesh hmesh_nonneg)
    hmesh_tendsto hscaledResidual_tendsto


theorem physicalIncidence_uniform_convergence_of_scaledExactBoundaryAndLaplacian
    (N : Nat → Nat) (hN : ∀ k, 0 < N k)
    (Phi : Complex → Complex) (mesh laplacianRate : Nat → Real)
    (lipschitzConstant : NNReal)
    (hmesh_nonneg : ∀ k, 0 ≤ mesh k)
    (hlaplacian_nonneg : ∀ k, 0 ≤ laplacianRate k)
    (hvertexFixed : ∀ k x,
      fkIsingSquareFullVertexFixedBoundary (N k) x →
        (Phi (fullSquareScaledVertexEmbedding
          (N k) (mesh k) x)).im = 0)
    (hfaceFixed : ∀ k c,
      fkIsingSquareFullFaceFixedBoundary (N k) c →
        (Phi (fullSquareScaledFaceEmbedding
          (N k) (mesh k) c)).im = 1)
    (hvertexFree : ∀ k x,
      ¬ fkIsingSquareFullVertexFixedBoundary (N k) x →
      0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x →
        (Phi (fullSquareScaledVertexEmbedding
          (N k) (mesh k) x)).im = 1)
    (hfaceFree : ∀ k c,
      ¬ fkIsingSquareFullFaceFixedBoundary (N k) c →
      0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c →
        (Phi (fullSquareScaledFaceEmbedding
          (N k) (mesh k) c)).im = 0)
    (hvertexLaplacian : ∀ k x,
      ¬ fkIsingSquareFullVertexFixedBoundary (N k) x →
        |isingFiniteGraphLaplacian
          (fkIsingSquareFullVertexGraph (N k))
          (fun y ↦ (Phi (fullSquareScaledVertexEmbedding
            (N k) (mesh k) y)).im) x| ≤ laplacianRate k)
    (hfaceLaplacian : ∀ k c,
      ¬ fkIsingSquareFullFaceFixedBoundary (N k) c →
        |isingFiniteGraphLaplacian
          (fkIsingSquareFullFaceGraph (N k))
          (fun d ↦ (Phi (fullSquareScaledFaceEmbedding
            (N k) (mesh k) d)).im) c| ≤ laplacianRate k)
    (hPhi : LipschitzWith lipschitzConstant (fun z ↦ (Phi z).im))
    (hmesh_tendsto : Tendsto mesh atTop (nhds 0))
    (hscaledLaplacian_tendsto : Tendsto
      (fun k ↦ laplacianRate k * (N k : Real) ^ 2) atTop (nhds 0)) :
    ∀ eta : Real, 0 < eta → ∀ᶠ k in atTop,
      ∀ e : FKIsingSquareInteriorRadialIncidence (N k) (hN k),
        |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (N k) (hN k)).vertexPrimitive
            (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e) -
              (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k)
                (fkIsingSquareInteriorRadialEndpoint
                  (N k) (hN k) e))).im| < eta ∧
          |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (N k) (hN k)).facePrimitive
            (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e) -
              (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k)
                (fkIsingSquareInteriorRadialEndpoint
                  (N k) (hN k) e))).im| < eta := by
  apply physicalIncidence_uniform_convergence_of_scaledMeshAndQuadraticResidual
    N hN Phi mesh laplacianRate 0 lipschitzConstant hmesh_nonneg
      (le_refl 0) hlaplacian_nonneg
  · intro k x hx
    simp [hvertexFixed k x hx]
  · intro k c hc
    simp [hfaceFixed k c hc]
  · intro k x hx
    simpa using
      (vertexSampled_robinResidual_le_of_laplacian_and_trace
        (N k) (fullSquareScaledVertexEmbedding (N k) (mesh k)) Phi
        (laplacianRate k) 0 (le_refl 0) (hvertexLaplacian k)
        (fun y hyFixed hy ↦ by simp [hvertexFree k y hyFixed hy]) x hx)
  · intro k c hc
    simpa using
      (faceSampled_robinResidual_le_of_laplacian_and_trace
        (N k) (fullSquareScaledFaceEmbedding (N k) (mesh k)) Phi
        (laplacianRate k) 0 (le_refl 0) (hfaceLaplacian k)
        (fun d hdFixed hd ↦ by simp [hfaceFree k d hdFixed hd]) c hc)
  · exact hPhi
  · exact hmesh_tendsto
  · exact hscaledLaplacian_tendsto

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality

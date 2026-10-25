/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRobinCompatibility.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicProjectedFullMedialInterpolation.Part5
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareCaratheodory.Part5
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryLayerConsistency.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCalibratedRobinConsistency
import Structure.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRobinCompatibility.Part2


namespace StatMech.Universality

open Filter Metric Set Topology

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem PhysicalSplitRobinConsistencyInputs.ofFourthOrderAndLipschitz
    {N : Nat → Nat} {hN : ∀ k, 0 < N k}
    {Phi : Complex → Complex} {mesh : Nat → Real}
    (Hfourth : PhysicalFourthOrderBulkData N Phi mesh)
    (L : NNReal) (hPhi : LipschitzWith L (fun z ↦ (Phi z).im))
    (hmesh_nonneg : ∀ k, 0 ≤ mesh k)
    (hvertexFixed : ∀ k x,
      fkIsingSquareFullVertexFixedBoundary (N k) x →
        (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im = 0)
    (hfaceFixed : ∀ k c,
      fkIsingSquareFullFaceFixedBoundary (N k) c →
        (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im = 1)
    (hvertexFree : ∀ k x,
      ¬ fkIsingSquareFullVertexFixedBoundary (N k) x →
      0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x →
        (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im = 1)
    (hfaceFree : ∀ k c,
      ¬ fkIsingSquareFullFaceFixedBoundary (N k) c →
      0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c →
        (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im = 0)
    (hmesh_tendsto : Tendsto mesh atTop (nhds 0))
    (hscaledFourth_tendsto : Tendsto
      (fun k ↦ |mesh k| ^ 4 * (N k : Real) ^ 2) atTop (nhds 0)) :
    PhysicalSplitRobinConsistencyInputs N hN Phi mesh
      (fun k ↦ (Hfourth.boundOne + Hfourth.boundTwo) * |mesh k| ^ 4 / 12)
      (fun k ↦ 8 * (L : Real) * |mesh k|) := by
  refine
    { mesh_nonneg := hmesh_nonneg
      bulk_nonneg := ?_
      layer_nonneg := ?_
      vertexFixed := hvertexFixed
      faceFixed := hfaceFixed
      vertexFree := hvertexFree
      faceFree := hfaceFree
      vertexBulk := ?_
      faceBulk := ?_
      vertexLayer := ?_
      faceLayer := ?_
      scaledBulk_tendsto := ?_
      layer_tendsto := ?_
      mesh_tendsto := hmesh_tendsto }
  · intro k
    exact div_nonneg
      (mul_nonneg Hfourth.boundSum_nonneg (pow_nonneg (abs_nonneg _) 4))
      (by norm_num)
  · intro k
    exact mul_nonneg
      (mul_nonneg (by norm_num) L.2) (abs_nonneg _)
  · intro k x hfixed hghost
    exact Hfourth.vertexLaplacian k x hfixed hghost
  · intro k c hfixed hghost
    exact Hfourth.faceLaplacian k c hfixed hghost
  · intro k x _hfixed _hghost
    exact fullSquareScaledVertex_sampledLaplacian_le_lipschitz
      (N k) (mesh k) Phi L hPhi x
  · intro k c _hfixed _hghost
    exact fullSquareScaledFace_sampledLaplacian_le_lipschitz
      (N k) (mesh k) Phi L hPhi c
  · have hconstant : Tendsto
        (fun _ : Nat ↦ (Hfourth.boundOne + Hfourth.boundTwo) / 12)
        atTop (nhds ((Hfourth.boundOne + Hfourth.boundTwo) / 12)) :=
      tendsto_const_nhds
    have hproduct := hconstant.mul hscaledFourth_tendsto
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hproduct
  · have habs : Tendsto (fun k ↦ |mesh k|) atTop (nhds 0) := by
      simpa using hmesh_tendsto.abs
    simpa using tendsto_const_nhds.mul habs


theorem PhysicalSplitRobinConsistencyInputs.primitive_convergence
    {N : Nat → Nat} {hN : ∀ k, 0 < N k}
    {Phi : Complex → Complex}
    {mesh bulkRate layerRate : Nat → Real}
    (H : PhysicalSplitRobinConsistencyInputs
      N hN Phi mesh bulkRate layerRate)
    (lipschitzConstant : NNReal)
    (hPhi : LipschitzWith lipschitzConstant (fun z ↦ (Phi z).im)) :
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
  let upper : Nat → Real := fun k ↦
    vertexBarrierGrowthConstant * (bulkRate k * (N k : Real) ^ 2) +
      (1 / isingFermionicGhostCoefficient) * layerRate k +
      (lipschitzConstant : Real) * mesh k
  have hupper : Tendsto upper atTop (nhds 0) := by
    have hbulk : Tendsto
        (fun k ↦ vertexBarrierGrowthConstant *
          (bulkRate k * (N k : Real) ^ 2)) atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul H.scaledBulk_tendsto
    have hlayer : Tendsto
        (fun k ↦ (1 / isingFermionicGhostCoefficient) * layerRate k)
        atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul H.layer_tendsto
    have hmesh : Tendsto
        (fun k ↦ (lipschitzConstant : Real) * mesh k)
        atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul H.mesh_tendsto
    simpa [upper] using (hbulk.add hlayer).add hmesh
  intro eta heta
  have heventually : ∀ᶠ k in atTop, dist (upper k) 0 < eta :=
    (Metric.tendsto_nhds.1 hupper) eta heta
  filter_upwards [heventually] with k hk
  intro e
  have hupper_nonneg : 0 ≤ upper k := by
    dsimp only [upper]
    exact add_nonneg
      (add_nonneg
        (mul_nonneg vertexBarrierGrowthConstant_nonneg
          (mul_nonneg (H.bulk_nonneg k) (sq_nonneg _)))
        (mul_nonneg
          (div_nonneg (by norm_num)
            isingFermionicGhostCoefficient_pos.le)
          (H.layer_nonneg k)))
      (mul_nonneg lipschitzConstant.2 (H.mesh_nonneg k))
  have hk' : upper k < eta := by
    simpa [Real.dist_eq, abs_of_nonneg hupper_nonneg] using hk
  let vertexEmbedding :=
    fullSquareScaledVertexEmbedding (N k) (mesh k)
  let faceEmbedding :=
    fullSquareScaledFaceEmbedding (N k) (mesh k)
  let x := fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e
  let c := fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e
  have hv := vertexSampled_target_error_le_split
    (N k) (hN k) vertexEmbedding Phi (bulkRate k) (layerRate k)
    (H.bulk_nonneg k) (H.layer_nonneg k) (H.vertexBulk k)
    (H.vertexLayer k) (H.vertexFree k) (some x)
  have hvBoundary : vertexBoundaryConsistencyError (N k) (hN k)
      (vertexSampledImaginaryTarget (N k) vertexEmbedding Phi) = 0 :=
    vertexSampled_boundaryConsistencyError_eq_zero
      (N k) (hN k) vertexEmbedding Phi (H.vertexFixed k)
  have hvBarrier := vertexExplicitPoissonBarrierBound_le_growth
    (N k) (hN k)
  have hv' : |vertexDirichlet (N k) (hN k) (some x) -
      (Phi (vertexEmbedding x)).im| ≤ upper k := by
    calc
      _ ≤ vertexBoundaryConsistencyError (N k) (hN k)
            (vertexSampledImaginaryTarget (N k) vertexEmbedding Phi) +
          bulkRate k * vertexExplicitPoissonBarrierBound (N k) +
          layerRate k * (1 / isingFermionicGhostCoefficient) := hv
      _ ≤ 0 + bulkRate k *
            (vertexBarrierGrowthConstant * (N k : Real) ^ 2) +
          layerRate k * (1 / isingFermionicGhostCoefficient) := by
        rw [hvBoundary]
        gcongr
        exact H.bulk_nonneg k
      _ ≤ upper k := by
        dsimp only [upper]
        have hm : 0 ≤ (lipschitzConstant : Real) * mesh k :=
          mul_nonneg lipschitzConstant.2 (H.mesh_nonneg k)
        nlinarith
  have hf := faceSampled_target_error_le_split
    (N k) (hN k) faceEmbedding Phi (bulkRate k) (layerRate k)
    (H.bulk_nonneg k) (H.layer_nonneg k) (H.faceBulk k)
    (H.faceLayer k) (H.faceFree k) (some c)
  have hfBoundary : faceBoundaryConsistencyError (N k) (hN k)
      (faceSampledImaginaryTarget (N k) faceEmbedding Phi) = 0 :=
    faceSampled_boundaryConsistencyError_eq_zero
      (N k) (hN k) faceEmbedding Phi (H.faceFixed k)
  have hfBarrier : faceExplicitPoissonBarrierBound (N k) ≤
      vertexBarrierGrowthConstant * (N k : Real) ^ 2 := by
    calc
      faceExplicitPoissonBarrierBound (N k) =
          (1 / 2 : Real) * (N k : Real) ^ 2 := by
        unfold faceExplicitPoissonBarrierBound
        ring
      _ ≤ vertexBarrierGrowthConstant * (N k : Real) ^ 2 :=
        mul_le_mul_of_nonneg_right half_le_vertexBarrierGrowthConstant
          (sq_nonneg _)
  have hfOwn : |faceDirichlet (N k) (hN k) (some c) -
      (Phi (faceEmbedding c)).im| ≤
        vertexBarrierGrowthConstant * (bulkRate k * (N k : Real) ^ 2) +
          (1 / isingFermionicGhostCoefficient) * layerRate k := by
    calc
      _ ≤ faceBoundaryConsistencyError (N k) (hN k)
            (faceSampledImaginaryTarget (N k) faceEmbedding Phi) +
          bulkRate k * faceExplicitPoissonBarrierBound (N k) +
          layerRate k * (1 / isingFermionicGhostCoefficient) := hf
      _ ≤ 0 + bulkRate k *
            (vertexBarrierGrowthConstant * (N k : Real) ^ 2) +
          layerRate k * (1 / isingFermionicGhostCoefficient) := by
        rw [hfBoundary]
        gcongr
        exact H.bulk_nonneg k
      _ = _ := by ring
  have hmismatch : |(Phi (faceEmbedding c)).im -
      (Phi (vertexEmbedding x)).im| ≤
        (lipschitzConstant : Real) * mesh k := by
    rw [← Real.dist_eq]
    calc
      dist (Phi (faceEmbedding c)).im (Phi (vertexEmbedding x)).im ≤
          lipschitzConstant * dist (faceEmbedding c) (vertexEmbedding x) :=
        hPhi.dist_le_mul _ _
      _ ≤ lipschitzConstant * mesh k :=
        mul_le_mul_of_nonneg_left
          (fullSquareScaledEmbedding_incidenceDistance
            N hN mesh H.mesh_nonneg k e) lipschitzConstant.2
  have hf' : |faceDirichlet (N k) (hN k) (some c) -
      (Phi (vertexEmbedding x)).im| ≤ upper k := by
    rw [show faceDirichlet (N k) (hN k) (some c) -
        (Phi (vertexEmbedding x)).im =
      (faceDirichlet (N k) (hN k) (some c) -
        (Phi (faceEmbedding c)).im) +
      ((Phi (faceEmbedding c)).im - (Phi (vertexEmbedding x)).im) by ring]
    calc
      |_ + _| ≤ |faceDirichlet (N k) (hN k) (some c) -
          (Phi (faceEmbedding c)).im| +
        |(Phi (faceEmbedding c)).im -
          (Phi (vertexEmbedding x)).im| := abs_add_le _ _
      _ ≤ (vertexBarrierGrowthConstant *
            (bulkRate k * (N k : Real) ^ 2) +
          (1 / isingFermionicGhostCoefficient) * layerRate k) +
            (lipschitzConstant : Real) * mesh k :=
        add_le_add hfOwn hmismatch
      _ = upper k := by rfl
  have hphysical := physicalIncidence_close_of_dirichlet_close
    (N k) (hN k) e (Phi (vertexEmbedding x)).im (upper k) hv' hf'
  exact ⟨hphysical.1.trans_lt hk', hphysical.2.trans_lt hk'⟩


theorem PhysicalRobinConsistencyInputs.primitive_convergence
    {N : Nat → Nat} {hN : ∀ k, 0 < N k}
    {Phi : Complex → Complex} {mesh laplacianRate : Nat → Real}
    (H : PhysicalRobinConsistencyInputs N hN Phi mesh laplacianRate)
    (lipschitzConstant : NNReal)
    (hPhi : LipschitzWith lipschitzConstant (fun z ↦ (Phi z).im)) :
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
  exact physicalIncidence_uniform_convergence_of_scaledExactBoundaryAndLaplacian
    N hN Phi mesh laplacianRate lipschitzConstant H.mesh_nonneg
    H.laplacian_nonneg H.vertexFixed H.faceFixed H.vertexFree H.faceFree
    H.vertexLaplacian H.faceLaplacian hPhi H.mesh_tendsto
    H.scaledLaplacian_tendsto

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality

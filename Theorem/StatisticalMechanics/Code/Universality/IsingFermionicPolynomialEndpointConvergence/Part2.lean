/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPolynomialEndpointConvergence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicVertexCornerCardinality.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFaceCornerCardinality.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointInputAssembly.Part2
import Structure.StatisticalMechanics.Code.Universality.IsingFermionicPolynomialEndpointConvergence


namespace StatMech.Universality

open Filter

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem vertexEndpointPolynomialBound_nonneg (k : Nat) :
    0 <= vertexEndpointPolynomialBound k := by
  have hcoefficient : 0 < isingFermionicGhostCoefficient :=
    isingFermionicGhostCoefficient_pos
  unfold vertexEndpointPolynomialBound
  positivity

theorem faceEndpointPolynomialBound_nonneg (k : Nat) :
    0 <= faceEndpointPolynomialBound k := by
  have hcoefficient : 0 < isingFermionicGhostCoefficient :=
    isingFermionicGhostCoefficient_pos
  unfold faceEndpointPolynomialBound
  positivity


theorem PhysicalEndpointLocalizedRobinInputs.ofPolynomialData
    {Phi : Complex -> Complex}
    (Hfourth : PhysicalEndpointFourthOrderBulkData
      isingFermionicPolynomialSide Phi isingFermionicPolynomialMesh
      isingFermionicPolynomialRadius)
    (Hlayer : PhysicalEndpointLayerIncrementData
      isingFermionicPolynomialSide Phi isingFermionicPolynomialMesh
      isingFermionicPolynomialRadius)
    (hvertexFixed : forall k x,
      fkIsingSquareFullVertexFixedBoundary
        (isingFermionicPolynomialSide k) x ->
        (Phi (fullSquareScaledVertexEmbedding
          (isingFermionicPolynomialSide k)
          (isingFermionicPolynomialMesh k) x)).im = 0)
    (hfaceFixed : forall k c,
      fkIsingSquareFullFaceFixedBoundary
        (isingFermionicPolynomialSide k) c ->
        (Phi (fullSquareScaledFaceEmbedding
          (isingFermionicPolynomialSide k)
          (isingFermionicPolynomialMesh k) c)).im = 1)
    (hvertexFree : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary
        (isingFermionicPolynomialSide k) x) ->
      0 < fkIsingSquareFullVertexGhostMultiplicity
        (isingFermionicPolynomialSide k) x ->
        (Phi (fullSquareScaledVertexEmbedding
          (isingFermionicPolynomialSide k)
          (isingFermionicPolynomialMesh k) x)).im = 1)
    (hfaceFree : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary
        (isingFermionicPolynomialSide k) c) ->
      0 < fkIsingSquareFullFaceGhostMultiplicity
        (isingFermionicPolynomialSide k) c ->
        (Phi (fullSquareScaledFaceEmbedding
          (isingFermionicPolynomialSide k)
          (isingFermionicPolynomialMesh k) c)).im = 0)
    (hvertexRange : forall k x,
      0 <= (Phi (fullSquareScaledVertexEmbedding
        (isingFermionicPolynomialSide k)
        (isingFermionicPolynomialMesh k) x)).im /\
      (Phi (fullSquareScaledVertexEmbedding
        (isingFermionicPolynomialSide k)
        (isingFermionicPolynomialMesh k) x)).im <= 1)
    (hfaceRange : forall k c,
      0 <= (Phi (fullSquareScaledFaceEmbedding
        (isingFermionicPolynomialSide k)
        (isingFermionicPolynomialMesh k) c)).im /\
      (Phi (fullSquareScaledFaceEmbedding
        (isingFermionicPolynomialSide k)
        (isingFermionicPolynomialMesh k) c)).im <= 1) :
    PhysicalEndpointLocalizedRobinInputs
      isingFermionicPolynomialSide isingFermionicPolynomialSide_pos
      Phi isingFermionicPolynomialMesh isingFermionicPolynomialRadius
      (fun k =>
        (Hfourth.boundOne + Hfourth.boundTwo) *
          |isingFermionicPolynomialMesh k| ^ 4 / 12)
      (fun k => 4 * Hlayer.constant * isingFermionicPolynomialMesh k)
      (fun _ => 4) := by
  exact PhysicalEndpointLocalizedRobinInputs.ofLocalizedFourthOrderLayerAndRange
    Hfourth Hlayer isingFermionicPolynomialMesh_nonneg
    hvertexFixed hfaceFixed hvertexFree hfaceFree hvertexRange hfaceRange
    tendsto_isingFermionicPolynomialMesh_fourthOrder
    tendsto_isingFermionicPolynomialMesh


theorem PhysicalEndpointLocalizedRobinInputs.primitive_convergence_away_polynomial
    {Phi : Complex -> Complex} {mesh bulkRate layerRate : Nat -> Real}
    (H : PhysicalEndpointLocalizedRobinInputs
      isingFermionicPolynomialSide isingFermionicPolynomialSide_pos
      Phi mesh isingFermionicPolynomialRadius bulkRate layerRate
      (fun _ => 4))
    (mismatchRate : Nat -> Real)
    (hmismatch_nonneg : forall k, 0 <= mismatchRate k)
    (hmismatch : forall k e, PhysicalPolynomialEndpointSafe k e ->
      |(Phi (fullSquareScaledFaceEmbedding
          (isingFermionicPolynomialSide k) (mesh k)
          (fkIsingSquareFullFaceOfRadialIncidence
            (isingFermionicPolynomialSide k)
            (isingFermionicPolynomialSide_pos k) e))).im -
        (Phi (fullSquareScaledVertexEmbedding
          (isingFermionicPolynomialSide k) (mesh k)
          (fkIsingSquareInteriorRadialEndpoint
            (isingFermionicPolynomialSide k)
            (isingFermionicPolynomialSide_pos k) e))).im| <=
          mismatchRate k)
    (hmismatch_tendsto : Tendsto mismatchRate atTop (nhds 0)) :
    forall eta : Real, 0 < eta -> ∀ᶠ k in atTop,
      forall e : FKIsingSquareInteriorRadialIncidence
        (isingFermionicPolynomialSide k)
        (isingFermionicPolynomialSide_pos k),
        PhysicalPolynomialEndpointSafe k e ->
        |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (isingFermionicPolynomialSide k)
              (isingFermionicPolynomialSide_pos k)).vertexPrimitive
            (fkIsingSquareInteriorRadialEndpoint
              (isingFermionicPolynomialSide k)
              (isingFermionicPolynomialSide_pos k) e) -
              (Phi (fullSquareScaledVertexEmbedding
                (isingFermionicPolynomialSide k) (mesh k)
                (fkIsingSquareInteriorRadialEndpoint
                  (isingFermionicPolynomialSide k)
                  (isingFermionicPolynomialSide_pos k) e))).im| < eta /\
          |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (isingFermionicPolynomialSide k)
              (isingFermionicPolynomialSide_pos k)).facePrimitive
            (fkIsingSquareFullFaceOfRadialIncidence
              (isingFermionicPolynomialSide k)
              (isingFermionicPolynomialSide_pos k) e) -
              (Phi (fullSquareScaledVertexEmbedding
                (isingFermionicPolynomialSide k) (mesh k)
                (fkIsingSquareInteriorRadialEndpoint
                  (isingFermionicPolynomialSide k)
                  (isingFermionicPolynomialSide_pos k) e))).im| < eta := by
  apply H.primitive_convergence_away PhysicalPolynomialEndpointSafe
    vertexEndpointPolynomialBound faceEndpointPolynomialBound mismatchRate
  · exact vertexEndpointPolynomialBound_nonneg
  · exact faceEndpointPolynomialBound_nonneg
  · exact hmismatch_nonneg
  · intro k e hsafe
    simpa [isingFermionicPolynomialSide,
      isingFermionicPolynomialRadius] using
      vertexMarkedEndpointBarrier_le_polynomialBound_of_halfColumn
        k (fkIsingSquareInteriorRadialEndpoint
          (isingFermionicPolynomialSide k)
          (isingFermionicPolynomialSide_pos k) e)
        hsafe.vertexNotFixed hsafe.vertexRight hsafe.vertexBottom
        hsafe.vertexTop hsafe.vertexHalf
  · intro k e hsafe
    simpa [isingFermionicPolynomialSide,
      isingFermionicPolynomialRadius] using
      faceMarkedEndpointBarrier_le_polynomialBound_of_halfColumn
        k (fkIsingSquareFullFaceOfRadialIncidence
          (isingFermionicPolynomialSide k)
          (isingFermionicPolynomialSide_pos k) e)
        hsafe.faceNotFixed hsafe.faceHalf
  · exact hmismatch
  · exact tendsto_four_mul_vertexEndpointPolynomialBound
  · exact tendsto_four_mul_faceEndpointPolynomialBound
  · exact hmismatch_tendsto


theorem PhysicalEndpointLocalizedRobinInputs.primitive_convergence_away_polynomial_of_lipschitz
    {Phi : Complex -> Complex} {mesh bulkRate layerRate : Nat -> Real}
    (H : PhysicalEndpointLocalizedRobinInputs
      isingFermionicPolynomialSide isingFermionicPolynomialSide_pos
      Phi mesh isingFermionicPolynomialRadius bulkRate layerRate
      (fun _ => 4))
    (L : NNReal) (hPhi : LipschitzWith L (fun z => (Phi z).im)) :
    forall eta : Real, 0 < eta -> ∀ᶠ k in atTop,
      forall e : FKIsingSquareInteriorRadialIncidence
        (isingFermionicPolynomialSide k)
        (isingFermionicPolynomialSide_pos k),
        PhysicalPolynomialEndpointSafe k e ->
        |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (isingFermionicPolynomialSide k)
              (isingFermionicPolynomialSide_pos k)).vertexPrimitive
            (fkIsingSquareInteriorRadialEndpoint
              (isingFermionicPolynomialSide k)
              (isingFermionicPolynomialSide_pos k) e) -
              (Phi (fullSquareScaledVertexEmbedding
                (isingFermionicPolynomialSide k) (mesh k)
                (fkIsingSquareInteriorRadialEndpoint
                  (isingFermionicPolynomialSide k)
                  (isingFermionicPolynomialSide_pos k) e))).im| < eta /\
          |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (isingFermionicPolynomialSide k)
              (isingFermionicPolynomialSide_pos k)).facePrimitive
            (fkIsingSquareFullFaceOfRadialIncidence
              (isingFermionicPolynomialSide k)
              (isingFermionicPolynomialSide_pos k) e) -
              (Phi (fullSquareScaledVertexEmbedding
                (isingFermionicPolynomialSide k) (mesh k)
                (fkIsingSquareInteriorRadialEndpoint
                  (isingFermionicPolynomialSide k)
                  (isingFermionicPolynomialSide_pos k) e))).im| < eta := by
  apply H.primitive_convergence_away_polynomial
    (fun k => (L : Real) * mesh k)
  · intro k
    exact mul_nonneg L.2 (H.mesh_nonneg k)
  · intro k e _hsafe
    rw [← Real.dist_eq]
    calc
      dist
          (Phi (fullSquareScaledFaceEmbedding
            (isingFermionicPolynomialSide k) (mesh k)
            (fkIsingSquareFullFaceOfRadialIncidence
              (isingFermionicPolynomialSide k)
              (isingFermionicPolynomialSide_pos k) e))).im
          (Phi (fullSquareScaledVertexEmbedding
            (isingFermionicPolynomialSide k) (mesh k)
            (fkIsingSquareInteriorRadialEndpoint
              (isingFermionicPolynomialSide k)
              (isingFermionicPolynomialSide_pos k) e))).im <=
          L * dist
            (fullSquareScaledFaceEmbedding
              (isingFermionicPolynomialSide k) (mesh k)
              (fkIsingSquareFullFaceOfRadialIncidence
                (isingFermionicPolynomialSide k)
                (isingFermionicPolynomialSide_pos k) e))
            (fullSquareScaledVertexEmbedding
              (isingFermionicPolynomialSide k) (mesh k)
              (fkIsingSquareInteriorRadialEndpoint
                (isingFermionicPolynomialSide k)
                (isingFermionicPolynomialSide_pos k) e)) :=
        hPhi.dist_le_mul _ _
      _ <= L * mesh k := by
        apply mul_le_mul_of_nonneg_left _ L.2
        exact fullSquareScaledEmbedding_incidenceDistance
          isingFermionicPolynomialSide isingFermionicPolynomialSide_pos
          mesh H.mesh_nonneg k e
  · simpa using tendsto_const_nhds.mul H.mesh_tendsto

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality

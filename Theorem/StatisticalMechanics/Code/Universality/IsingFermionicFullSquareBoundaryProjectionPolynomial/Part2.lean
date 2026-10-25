/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionPolynomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFullSquareBoundaryProjectionGeometry.Part4
import Def.StatisticalMechanics.Code.Universality.IsingFermionicFullSquareBoundaryProjectionPolynomial.Part2


namespace StatMech.Universality

open Filter Metric Set

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem
    PhysicalEndpointLocalizedMarkedClampedRobinInputs.primitive_convergence_away_projectionPolynomial
    {Phi : Complex -> Complex}
    {mesh boundaryRate bulkRate layerRate : Nat -> Real}
    (H : PhysicalEndpointLocalizedMarkedClampedRobinInputs
      isingFermionicProjectionPolynomialSide
      isingFermionicProjectionPolynomialSide_pos Phi mesh
      isingFermionicProjectionPolynomialRadius boundaryRate bulkRate layerRate
      (fun _ => 4 + 3 * isingFermionicGhostCoefficient))
    (mismatchRate : Nat -> Real)
    (hmismatch_nonneg : forall k, 0 <= mismatchRate k)
    (hmismatch : forall k e, PhysicalProjectionPolynomialEndpointSafe k e ->
      |(Phi (fullSquareScaledFaceEmbedding
          (isingFermionicProjectionPolynomialSide k) (mesh k)
          (fkIsingSquareFullFaceOfRadialIncidence
            (isingFermionicProjectionPolynomialSide k)
            (isingFermionicProjectionPolynomialSide_pos k) e))).im -
        (Phi (fullSquareScaledVertexEmbedding
          (isingFermionicProjectionPolynomialSide k) (mesh k)
          (fkIsingSquareInteriorRadialEndpoint
            (isingFermionicProjectionPolynomialSide k)
            (isingFermionicProjectionPolynomialSide_pos k) e))).im| <=
          mismatchRate k)
    (hmismatch_tendsto : Tendsto mismatchRate atTop (nhds 0)) :
    forall eta : Real, 0 < eta -> Filter.Eventually (fun k =>
      forall e : FKIsingSquareInteriorRadialIncidence
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicProjectionPolynomialSide_pos k),
        PhysicalProjectionPolynomialEndpointSafe k e ->
        |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (isingFermionicProjectionPolynomialSide k)
              (isingFermionicProjectionPolynomialSide_pos k)).vertexPrimitive
            (fkIsingSquareInteriorRadialEndpoint
              (isingFermionicProjectionPolynomialSide k)
              (isingFermionicProjectionPolynomialSide_pos k) e) -
              (Phi (fullSquareScaledVertexEmbedding
                (isingFermionicProjectionPolynomialSide k) (mesh k)
                (fkIsingSquareInteriorRadialEndpoint
                  (isingFermionicProjectionPolynomialSide k)
                  (isingFermionicProjectionPolynomialSide_pos k) e))).im| < eta /\
          |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (isingFermionicProjectionPolynomialSide k)
              (isingFermionicProjectionPolynomialSide_pos k)).facePrimitive
            (fkIsingSquareFullFaceOfRadialIncidence
              (isingFermionicProjectionPolynomialSide k)
              (isingFermionicProjectionPolynomialSide_pos k) e) -
              (Phi (fullSquareScaledVertexEmbedding
                (isingFermionicProjectionPolynomialSide k) (mesh k)
                (fkIsingSquareInteriorRadialEndpoint
                  (isingFermionicProjectionPolynomialSide k)
                  (isingFermionicProjectionPolynomialSide_pos k) e))).im| < eta)
      atTop := by
  apply H.primitive_convergence_away
    PhysicalProjectionPolynomialEndpointSafe
    (fun k => vertexEndpointPolynomialBound (k + 1))
    (fun k => faceEndpointPolynomialBound (k + 1)) mismatchRate
  · exact fun k => vertexEndpointPolynomialBound_nonneg (k + 1)
  · exact fun k => faceEndpointPolynomialBound_nonneg (k + 1)
  · exact hmismatch_nonneg
  · intro k e hsafe
    exact hsafe.vertexNotFixed
  · intro k e hsafe
    exact hsafe.faceNotFixed
  · intro k e hsafe
    simpa [isingFermionicProjectionPolynomialSide,
      isingFermionicProjectionPolynomialRadius,
      isingFermionicPolynomialSide, isingFermionicPolynomialRadius] using
      vertexMarkedEndpointBarrier_le_polynomialBound_of_halfColumn
        (k + 1) (fkIsingSquareInteriorRadialEndpoint
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicProjectionPolynomialSide_pos k) e)
        hsafe.vertexNotFixed hsafe.vertexRight hsafe.vertexBottom
        hsafe.vertexTop hsafe.vertexHalf
  · intro k e hsafe
    simpa [isingFermionicProjectionPolynomialSide,
      isingFermionicProjectionPolynomialRadius,
      isingFermionicPolynomialSide, isingFermionicPolynomialRadius] using
      faceMarkedEndpointBarrier_le_polynomialBound_of_halfColumn
        (k + 1) (fkIsingSquareFullFaceOfRadialIncidence
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicProjectionPolynomialSide_pos k) e)
        hsafe.faceNotFixed hsafe.faceHalf
  · exact hmismatch
  · simpa using
      (tendsto_const_nhds.mul tendsto_vertexEndpointPolynomialBound).comp
        (tendsto_add_atTop_nat 1)
  · simpa using
      (tendsto_const_nhds.mul tendsto_faceEndpointPolynomialBound).comp
        (tendsto_add_atTop_nat 1)
  · exact hmismatch_tendsto

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality

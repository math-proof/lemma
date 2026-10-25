/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionPolynomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFullSquareBoundaryProjectionGeometry.Part4
import Def.StatisticalMechanics.Code.Universality.IsingFermionicFullSquareBoundaryProjectionPolynomial


namespace StatMech.Universality

open Filter Metric Set

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem isingFermionicProjectionPolynomialSide_pos (k : Nat) :
    0 < isingFermionicProjectionPolynomialSide k := by
  exact isingFermionicPolynomialSide_pos (k + 1)

theorem isingFermionicProjectionPolynomialRadius_pos (k : Nat) :
    0 < isingFermionicProjectionPolynomialRadius k := by
  simp [isingFermionicProjectionPolynomialRadius,
    isingFermionicPolynomialRadius]

theorem isingFermionicProjectionPolynomialRadius_two_le (k : Nat) :
    2 <= isingFermionicProjectionPolynomialRadius k := by
  simp [isingFermionicProjectionPolynomialRadius,
    isingFermionicPolynomialRadius]

theorem isingFermionicProjectionPolynomialMesh_nonneg (k : Nat) :
    0 <= isingFermionicProjectionPolynomialMesh k := by
  exact isingFermionicPolynomialMesh_nonneg (k + 1)

theorem tendsto_isingFermionicProjectionPolynomialMesh :
    Tendsto isingFermionicProjectionPolynomialMesh atTop (nhds 0) := by
  exact tendsto_isingFermionicPolynomialMesh.comp (tendsto_add_atTop_nat 1)

theorem tendsto_isingFermionicProjectionPolynomialMesh_fourthOrder :
    Tendsto (fun k =>
      |isingFermionicProjectionPolynomialMesh k| ^ 4 *
        (isingFermionicProjectionPolynomialSide k : Real) ^ 2)
      atTop (nhds 0) := by
  simpa [isingFermionicProjectionPolynomialMesh,
    isingFermionicProjectionPolynomialSide] using
    tendsto_isingFermionicPolynomialMesh_fourthOrder.comp
      (tendsto_add_atTop_nat 1)

theorem
    tendsto_isingFermionicProjectionQuadraticLipschitz_mul_polynomialMesh
    (C : NNReal) :
    Tendsto (fun k =>
      (isingFermionicQuadraticLipschitzConstant C (k + 1) : Real) *
        isingFermionicProjectionPolynomialMesh k) atTop (nhds 0) := by
  simpa [isingFermionicProjectionPolynomialMesh] using
    (tendsto_isingFermionicQuadraticLipschitz_mul_polynomialMesh C).comp
      (tendsto_add_atTop_nat 1)


theorem
    PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofPolynomialTailCarrierSideTracesAndRange
    {Phi : Complex -> Complex}
    (Hfourth : PhysicalEndpointFourthOrderBulkData
      isingFermionicProjectionPolynomialSide Phi
      isingFermionicProjectionPolynomialMesh
      isingFermionicProjectionPolynomialRadius)
    (Hlayer : PhysicalEndpointLayerIncrementData
      isingFermionicProjectionPolynomialSide Phi
      isingFermionicProjectionPolynomialMesh
      isingFermionicProjectionPolynomialRadius)
    (C : NNReal)
    (hPhi : forall k,
      LipschitzOnWith (isingFermionicQuadraticLipschitzConstant C (k + 1))
        (fun z => (Phi z).im)
        (fullSquareOrdinaryBoundaryProjectionCarrier
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicProjectionPolynomialMesh k)
          (isingFermionicProjectionPolynomialRadius k)))
    (hleftTrace : forall k,
      Set.EqOn (fun z => (Phi z).im) (fun _ => 0)
        (fullSquareScaledLeftSide
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicProjectionPolynomialMesh k)))
    (hfreeTrace : forall k,
      Set.EqOn (fun z => (Phi z).im) (fun _ => 1)
        (fullSquareScaledFreeSides
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicProjectionPolynomialMesh k)))
    (hvertexRange : forall k x,
      0 <= (Phi (fullSquareScaledVertexEmbedding
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicProjectionPolynomialMesh k) x)).im /\
      (Phi (fullSquareScaledVertexEmbedding
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicProjectionPolynomialMesh k) x)).im <= 1)
    (hfaceRange : forall k c,
      0 <= (Phi (fullSquareScaledFaceEmbedding
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicProjectionPolynomialMesh k) c)).im /\
      (Phi (fullSquareScaledFaceEmbedding
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicProjectionPolynomialMesh k) c)).im <= 1) :
    PhysicalEndpointLocalizedMarkedClampedRobinInputs
      isingFermionicProjectionPolynomialSide
      isingFermionicProjectionPolynomialSide_pos Phi
      isingFermionicProjectionPolynomialMesh
      isingFermionicProjectionPolynomialRadius
      (fun k =>
        (isingFermionicQuadraticLipschitzConstant C (k + 1) : Real) *
          isingFermionicProjectionPolynomialMesh k)
      (fun k => (Hfourth.boundOne + Hfourth.boundTwo) *
        |isingFermionicProjectionPolynomialMesh k| ^ 4 / 12)
      (fun k => (4 * Hlayer.constant) *
          isingFermionicProjectionPolynomialMesh k +
        (3 * isingFermionicGhostCoefficient) *
          ((isingFermionicQuadraticLipschitzConstant C (k + 1) : Real) *
            isingFermionicProjectionPolynomialMesh k))
      (fun _ => 4 + 3 * isingFermionicGhostCoefficient) := by
  exact
    PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofCarrierSideTracesAndRange
      Hfourth Hlayer
      (fun k => isingFermionicQuadraticLipschitzConstant C (k + 1))
      hPhi hleftTrace hfreeTrace
      isingFermionicProjectionPolynomialRadius_pos
      isingFermionicProjectionPolynomialRadius_two_le
      isingFermionicProjectionPolynomialMesh_nonneg
      hvertexRange hfaceRange
      tendsto_isingFermionicProjectionPolynomialMesh_fourthOrder
      (tendsto_isingFermionicProjectionQuadraticLipschitz_mul_polynomialMesh C)
      tendsto_isingFermionicProjectionPolynomialMesh


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality

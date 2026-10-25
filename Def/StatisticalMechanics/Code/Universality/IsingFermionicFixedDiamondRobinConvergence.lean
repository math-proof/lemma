/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFixedDiamondRobinConvergence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFullSquareBoundaryProjectionAnalyticCollar
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointRadialPointGreen
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFixedDiamondRobinConvergence


namespace StatMech.Universality

open Filter Metric Set

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

def isingFermionicFixedDiamondOrdinaryLowerTraceCarrier : Set Complex :=
  {z |
    (∃ k x,
      fkIsingSquareFullVertexFixedBoundary
          (isingFermionicProjectionPolynomialSide k) x ∧
      Not (0 < fkIsingSquareFullVertexGhostMultiplicity
        (isingFermionicProjectionPolynomialSide k) x) ∧
      z = fullSquareVertexBoundaryProjection
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicFixedDiamondMesh k) x) ∨
    (∃ k c,
      Not (fkIsingSquareFullFaceFixedBoundary
        (isingFermionicProjectionPolynomialSide k) c) ∧
      0 < fkIsingSquareFullFaceGhostMultiplicity
        (isingFermionicProjectionPolynomialSide k) c ∧
      Not (faceMarkedEndpointLayer
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicProjectionPolynomialRadius k) (some c)) ∧
      z = fullSquareFaceFreeBoundaryProjection
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicFixedDiamondMesh k) c)}


def isingFermionicFixedDiamondOrdinaryUpperTraceCarrier : Set Complex :=
  {z |
    (∃ k c,
      fkIsingSquareFullFaceFixedBoundary
          (isingFermionicProjectionPolynomialSide k) c ∧
      Not (0 < fkIsingSquareFullFaceGhostMultiplicity
        (isingFermionicProjectionPolynomialSide k) c) ∧
      z = fullSquareFaceFixedBoundaryProjection
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicFixedDiamondMesh k) c) ∨
    (∃ k x,
      Not (fkIsingSquareFullVertexFixedBoundary
        (isingFermionicProjectionPolynomialSide k) x) ∧
      0 < fkIsingSquareFullVertexGhostMultiplicity
        (isingFermionicProjectionPolynomialSide k) x ∧
      Not (vertexMarkedEndpointLayer
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicProjectionPolynomialRadius k) (some x)) ∧
      z = fullSquareVertexFreeBoundaryProjection
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicFixedDiamondMesh k) x)}


noncomputable def fixedDiamondLayerIncrementDataOfLipschitz
    {Phi : Complex -> Complex} (L : NNReal)
    (hPhi : LipschitzOnWith L (fun z => (Phi z).im)
      isingFermionicFixedClosedDiamond) :
    PhysicalEndpointLayerIncrementData
      isingFermionicProjectionPolynomialSide Phi
      isingFermionicFixedDiamondMesh
      isingFermionicProjectionPolynomialRadius :=
  PhysicalEndpointLayerIncrementData.ofLipschitzOn
    isingFermionicFixedClosedDiamond L hPhi
    isingFermionicFixedDiamondMesh_nonneg
    (fun k x _hfixed _hghost _hendpoint =>
      ⟨fullSquareScaledVertexEmbedding_mem_fixedClosedDiamond k x,
        fun y _hxy =>
          fullSquareScaledVertexEmbedding_mem_fixedClosedDiamond k y⟩)
    (fun k c _hfixed _hghost _hendpoint =>
      ⟨fullSquareScaledFaceEmbedding_mem_fixedClosedDiamond k c,
        fun d _hcd =>
          fullSquareScaledFaceEmbedding_mem_fixedClosedDiamond k d⟩)


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality

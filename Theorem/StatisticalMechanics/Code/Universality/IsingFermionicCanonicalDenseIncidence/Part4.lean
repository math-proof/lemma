/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCanonicalDenseIncidence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDenseIncidencePrimitiveBridge.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIncidence.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part17
import Def.StatisticalMechanics.Code.Universality.IsingFermionicCanonicalDenseIncidence.Part4
open Filter Set Topology


namespace StatMech.Universality

noncomputable section

@[simp] theorem fkIsingSquareInteriorRadialIncidenceOfInt_endpoint
    (n : Nat) (hn : 0 < n) (x y : Int)
    (hxy : -(n : Int) ≤ x ∧ x < n ∧
      -(n : Int) ≤ y ∧ y < n) :
    fkIsingSquareInteriorRadialEndpoint n hn
        (fkIsingSquareInteriorRadialIncidenceOfInt n hn x y hxy) =
      fkIsingSquareFullVertexOfInt n x y
        ⟨hxy.1, le_of_lt hxy.2.1⟩
        ⟨hxy.2.2.1, le_of_lt hxy.2.2.2⟩ := by
  simp [fkIsingSquareInteriorRadialIncidenceOfInt]


theorem fullSquareScaledVertexEmbedding_fullVertexOfInt
    (n : Nat) (scale : Real) (x y : Int)
    (hx : -(n : Int) ≤ x ∧ x ≤ n)
    (hy : -(n : Int) ≤ y ∧ y ≤ n) :
    FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareScaledVertexEmbedding
        n scale (fkIsingSquareFullVertexOfInt n x y hx hy) =
      (scale : Complex) *
        (((x + y : Int) : Real) + ((x - y : Int) : Real) * Complex.I) := by
  simp [FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareScaledVertexEmbedding,
    FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareScaledCoordinateEmbedding,
    fkIsingSquareFullVertexCoordinate, fkIsingSquareFullVertexOfInt,
    fkIsingSquareWiredIntPoint, Algebra.smul_def]


end
end StatMech.Universality

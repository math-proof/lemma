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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPolynomialEndpointConvergence


namespace StatMech.Universality

open Filter

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

structure PhysicalPolynomialEndpointSafe (k : Nat)
    (e : FKIsingSquareInteriorRadialIncidence
      (isingFermionicPolynomialSide k)
      (isingFermionicPolynomialSide_pos k)) : Prop where
  vertexNotFixed : Not (fkIsingSquareFullVertexFixedBoundary
    (isingFermionicPolynomialSide k)
    (fkIsingSquareInteriorRadialEndpoint
      (isingFermionicPolynomialSide k)
      (isingFermionicPolynomialSide_pos k) e))
  vertexRight :
    (fkIsingSquareInteriorRadialEndpoint
      (isingFermionicPolynomialSide k)
      (isingFermionicPolynomialSide_pos k) e).1 0 <
        (isingFermionicPolynomialSide k : Int)
  vertexBottom :
    -(isingFermionicPolynomialSide k : Int) <
      (fkIsingSquareInteriorRadialEndpoint
        (isingFermionicPolynomialSide k)
        (isingFermionicPolynomialSide_pos k) e).1 1
  vertexTop :
    (fkIsingSquareInteriorRadialEndpoint
      (isingFermionicPolynomialSide k)
      (isingFermionicPolynomialSide_pos k) e).1 1 <
        (isingFermionicPolynomialSide k : Int)
  vertexHalf :
    ((isingFermionicPolynomialSide k : Real) / 2) <=
      fullVertexColumnIndex (isingFermionicPolynomialSide k)
        (fkIsingSquareInteriorRadialEndpoint
          (isingFermionicPolynomialSide k)
          (isingFermionicPolynomialSide_pos k) e)
  faceNotFixed : Not (fkIsingSquareFullFaceFixedBoundary
    (isingFermionicPolynomialSide k)
    (fkIsingSquareFullFaceOfRadialIncidence
      (isingFermionicPolynomialSide k)
      (isingFermionicPolynomialSide_pos k) e))
  faceHalf :
    ((isingFermionicPolynomialSide k : Real) / 2) <=
      (fkIsingSquareFullFaceOfRadialIncidence
        (isingFermionicPolynomialSide k)
        (isingFermionicPolynomialSide_pos k) e).1.1

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricJacobian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddSymmetricCovering
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheJacobianStability.Part4
import Mathlib.LinearAlgebra.Matrix.Gershgorin
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

def sixVertexOddNegativeCoordinateIndex (m : Nat) (k : Fin m) :
    Fin ((m + 1) + m) := sixVertexOddNegativeIndex m k.rev

def sixVertexBetheOddPositiveHalfJacobianMatrix
    (N m : Nat) (c : Real) (q : Fin m → Real) :
    Matrix (Fin m) (Fin m) Real := fun j k =>
  let p := sixVertexOddSymmetricLift m q
  sixVertexBetheJacobianMatrix N ((m + 1) + m) c p
      (sixVertexOddPositiveIndex m j) (sixVertexOddPositiveIndex m k) -
    sixVertexBetheJacobianMatrix N ((m + 1) + m) c p
      (sixVertexOddPositiveIndex m j) (sixVertexOddNegativeCoordinateIndex m k)

end
end StatMech.FrontierD

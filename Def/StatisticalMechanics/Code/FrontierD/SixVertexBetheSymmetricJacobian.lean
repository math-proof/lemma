/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricJacobian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricAnalytic.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheJacobianStability.Part4
import Mathlib.LinearAlgebra.Matrix.Gershgorin
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

def sixVertexBethePositiveHalfJacobianMatrix
    (N m : Nat) (c : Real) (q : Fin m → Real) :
    Matrix (Fin m) (Fin m) Real := fun j k =>
  let p := sixVertexEvenSymmetricLift m q
  sixVertexBetheJacobianMatrix N (m + m) c p
      (Fin.natAdd m j) (Fin.natAdd m k) -
    sixVertexBetheJacobianMatrix N (m + m) c p
      (Fin.natAdd m j) (Fin.castAdd m k.rev)

end
end StatMech.FrontierD

module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricAnalytic.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheJacobianStability.Part4
public import Mathlib.LinearAlgebra.Matrix.Gershgorin
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricJacobian.Part2
open Finset Matrix


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricJacobian.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def sixVertexBethePositiveHalfScaledJacobianMatrix
    (N m : Nat) (c : Real) (q : Fin m → Real) :
    Matrix (Fin m) (Fin m) Real := fun j k =>
  sixVertexBethePositiveHalfJacobianMatrix N m c q j k *
    sixVertexPositiveHalfRootGap q k

end
end StatMech.FrontierD

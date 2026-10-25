/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricDensityJacobian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddSymmetricJacobian
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFiniteDensityLipschitz.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddSymmetricDensityJacobian.Part3
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

def sixVertexBetheOddPositiveHalfScaledJacobianMatrix
    (N m : Nat) (c : Real) (q : Fin m → Real) :
    Matrix (Fin m) (Fin m) Real := fun j k =>
  sixVertexBetheOddPositiveHalfJacobianMatrix N m c q j k *
    sixVertexOddPositiveHalfRootGap q k

end
end StatMech.FrontierD

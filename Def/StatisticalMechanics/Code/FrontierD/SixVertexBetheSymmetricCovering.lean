/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricCovering.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricJacobian.Part3
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexEvenPositiveHalfProjection (m : Nat) :
    (Fin (m + m) → Real) →L[Real] (Fin m → Real) :=
  ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (Fin.natAdd m j)

end
end StatMech.FrontierD

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricAnalytic.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddSymmetricAnalytic.Part2
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexOddSymmetricBetheRootJacobian
    (N m : Nat) (c : Real) (q : Fin m → Real) :
    (Fin m → Real) →L[Real] (Fin m → Real) :=
  fderiv Real (sixVertexOddSymmetricBetheResidual N m c) q

end
end StatMech.FrontierD

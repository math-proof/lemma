/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheLocalAnalytic.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricAnalytic.Part2
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexEvenSymmetricBetheRootJacobian
    (N m : Nat) (c : Real) (q : Fin m → Real) :
    (Fin m → Real) →L[Real] (Fin m → Real) :=
  fderiv Real (sixVertexEvenSymmetricBetheResidual N m c) q

end
end StatMech.FrontierD

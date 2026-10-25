/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeAnisotropyRoots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnisotropyRoots.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeRoots.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeAnisotropyRoots.Part3
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexFixedChargeBetheRootError (r k : Nat)
    (j l : Fin (sixVertexFixedChargeBetheParticleCount r k))
    (c : Real) : Real :=
  sixVertexTheta c
      (sixVertexFixedChargeBetheRootAt r k j c)
      (sixVertexFixedChargeBetheRootAt r k l c) -
    (sixVertexFixedChargeBetheRootAt r k l c -
      sixVertexFixedChargeBetheRootAt r k j c)

end
end StatMech.FrontierD

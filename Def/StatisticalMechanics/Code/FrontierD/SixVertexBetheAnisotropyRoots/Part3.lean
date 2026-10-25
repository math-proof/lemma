/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnisotropyRoots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFiniteRoots.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnisotropyRoots.Part3
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexHalfFilledBetheRootError (k : Nat)
    (j l : Fin ((k + 1) + (k + 1))) (c : Real) : Real :=
  sixVertexTheta c
      (sixVertexHalfFilledBetheRootAt k j c)
      (sixVertexHalfFilledBetheRootAt k l c) -
    (sixVertexHalfFilledBetheRootAt k l c -
      sixVertexHalfFilledBetheRootAt k j c)

end
end StatMech.FrontierD

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnisotropyRoots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFiniteRoots.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnisotropyRoots
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexHalfFilledBetheRootAt (k : Nat)
    (j : Fin ((k + 1) + (k + 1))) (c : Real) : Real :=
  if hc : 2 < c then sixVertexHalfFilledBetheRoots hc k j else 0

end
end StatMech.FrontierD

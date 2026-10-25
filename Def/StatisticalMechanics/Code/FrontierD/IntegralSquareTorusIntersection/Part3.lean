/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.IntegralSquareTorusIntersection.Part2
open scoped BigOperators
open Finset


namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

namespace IntegralSquareTorusCycle

variable {L : Nat} [Fact (2 < L)]


def streamPotential (C : IntegralSquareTorusCycle L)
    (p : ZMod L × ZMod L) : Int :=
  ons_zmodPrefix (fun y => C.zeroFluxHorizontal (0, y)) p.2 -
    ons_zmodPrefix (fun x => C.zeroFluxVertical (x, p.2)) p.1

end IntegralSquareTorusCycle
end
end StatMech.FrontierD

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.IntegralSquareTorusIntersection
open scoped BigOperators
open Finset


namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

namespace IntegralSquareTorusCycle

variable {L : Nat} [Fact (2 < L)]


def zeroFluxHorizontal (C : IntegralSquareTorusCycle L)
    (p : ZMod L × ZMod L) : Int :=
  C.horizontal p - if p.2 = 0 then C.xFlux (-1) else 0


def zeroFluxVertical (C : IntegralSquareTorusCycle L)
    (p : ZMod L × ZMod L) : Int :=
  C.vertical p - if p.1 = 0 then C.yFlux (-1) else 0

end IntegralSquareTorusCycle
end
end StatMech.FrontierD

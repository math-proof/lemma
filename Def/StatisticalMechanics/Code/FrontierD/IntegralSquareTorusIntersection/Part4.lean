/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.IntegralSquareTorusIntersection.Part3
open scoped BigOperators
open Finset


namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

namespace IntegralSquareTorusCycle

variable {L : Nat} [Fact (2 < L)]


def intersection (C D : IntegralSquareTorusCycle L) : Int :=
  ∑ p : ZMod L × ZMod L,
    (C.horizontal p * D.vertical (p.1, p.2 - 1) -
      C.vertical p * D.horizontal (p.1 - 1, p.2))

end IntegralSquareTorusCycle
end
end StatMech.FrontierD

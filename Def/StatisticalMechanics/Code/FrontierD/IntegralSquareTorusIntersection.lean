/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part8
import Structure.StatisticalMechanics.Code.FrontierD.IntegralSquareTorusIntersection
open scoped BigOperators
open Finset


namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

namespace IntegralSquareTorusCycle

variable {L : Nat} [Fact (2 < L)]


def xFlux (C : IntegralSquareTorusCycle L) (x : ZMod L) : Int :=
  ∑ y : ZMod L, C.horizontal (x, y)


def yFlux (C : IntegralSquareTorusCycle L) (y : ZMod L) : Int :=
  ∑ x : ZMod L, C.vertical (x, y)

end IntegralSquareTorusCycle
end
end StatMech.FrontierD

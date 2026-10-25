/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.IntegralSquareTorusIntersection.Part6
open scoped BigOperators
open Finset


namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

namespace IntegralSquareTorusCycle

variable {L : Nat} [Fact (2 < L)]


def dartHorizontal (d : ons_Dart L) (p : ZMod L × ZMod L) : Int :=
  if d.2 = 0 then pointMass d.1 p
  else if d.2 = 2 then -pointMass (d.1.1 - 1, d.1.2) p
  else 0


def dartVertical (d : ons_Dart L) (p : ZMod L × ZMod L) : Int :=
  if d.2 = 1 then pointMass d.1 p
  else if d.2 = 3 then -pointMass (d.1.1, d.1.2 - 1) p
  else 0

end IntegralSquareTorusCycle
end
end StatMech.FrontierD

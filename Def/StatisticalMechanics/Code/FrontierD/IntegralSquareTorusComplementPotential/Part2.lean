/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusComplementPotential.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedBoundaryOpenPathPotential
import Instance.StatisticalMechanics.Code.FrontierD.IntegralSquareTorusComplementPotential


namespace StatMech.FrontierD

open StatMech.Onsager

open IntegralSquareTorusCycle

noncomputable section

variable {L : Nat} [Fact (8 < L)]

def integralSquareTorusPotentialIncrement
    (C : IntegralSquareTorusCycle L) (d : ons_Dart L) : Int :=
  C.streamPotential (ons_dirStep L d.2 d.1) - C.streamPotential d.1


def integralSquareTorusCycleListInteraction
    (C : IntegralSquareTorusCycle L) (l : List (ons_Dart L)) : Int :=
  ∑ p : ZMod L × ZMod L,
    (C.horizontal p *
        (l.map (fun d => dartVertical d (p.1, p.2 - 1))).sum -
      C.vertical p *
        (l.map (fun d => dartHorizontal d (p.1 - 1, p.2))).sum)

end
end StatMech.FrontierD

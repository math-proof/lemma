/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedInteractionCore.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedIntersection.Part2
open scoped BigOperators
open Finset


namespace StatMech.FrontierD

open StatMech.Onsager

open IntegralSquareTorusCycle

noncomputable section

variable {L : Nat} [Fact (8 < L)]

def fkRectRefinedScalePoint (p : Int × Int) : Int × Int :=
  (4 * p.1, 4 * p.2)


def fkRectRefinedScaleDart (d : FKRectIntegralSquareDart) :
    List FKRectIntegralSquareDart :=
  let p := fkRectRefinedScalePoint d.1
  match d.2 with
  | 0 => [(p, 0), ((p.1 + 1, p.2), 0), ((p.1 + 2, p.2), 0),
      ((p.1 + 3, p.2), 0)]
  | 1 => [(p, 1), ((p.1, p.2 + 1), 1), ((p.1, p.2 + 2), 1),
      ((p.1, p.2 + 3), 1)]
  | 2 => [(p, 2), ((p.1 - 1, p.2), 2), ((p.1 - 2, p.2), 2),
      ((p.1 - 3, p.2), 2)]
  | 3 => [(p, 3), ((p.1, p.2 - 1), 3), ((p.1, p.2 - 2), 3),
      ((p.1, p.2 - 3), 3)]


end
end StatMech.FrontierD

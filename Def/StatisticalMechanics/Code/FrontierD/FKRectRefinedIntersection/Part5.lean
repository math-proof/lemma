/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedInteractionCore.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedIntersection.Part5
open scoped BigOperators
open Finset


namespace StatMech.FrontierD

open StatMech.Onsager

open IntegralSquareTorusCycle

noncomputable section

variable {L : Nat} [Fact (8 < L)]

def fkRectMedialBoundaryPrimalSeamTrace
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus) :
    FKMedialDart R.medialTorus → Nat → Int × Int
  | _, 0 => (0, 0)
  | d, n + 1 =>
      let a := fkRectMedialBoundaryPrimalSeamIncrement R pairing d
      let z := fkRectMedialBoundaryPrimalSeamTrace R pairing
        (fkMedialBoundaryStep pairing d) n
      (a.1 + z.1, a.2 + z.2)


end
end StatMech.FrontierD

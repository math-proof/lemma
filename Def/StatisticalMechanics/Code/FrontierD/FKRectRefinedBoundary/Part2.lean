/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectMedialBoundaryWalk.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedBoundary


namespace StatMech.FrontierD

noncomputable section

def fkRectRefinedLocalDarts (pairing : Bool) (c : Int × Int)
    (side : FKMedialSide) : List FKRectIntegralSquareDart :=
  let p := fkRectRefinedDartPoint c side
  match pairing, side with
  | false, .west | false, .south => [(p, 0), ((p.1 + 1, p.2), 0)]
  | false, .east | false, .north => [(p, 2), ((p.1 - 1, p.2), 2)]
  | true, .west | true, .north => [(p, 1), ((p.1, p.2 + 1), 1)]
  | true, .east | true, .south => [(p, 3), ((p.1, p.2 - 1), 3)]

end
end StatMech.FrontierD

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryOrbitVisits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryOrbitReachability
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryOrbitVisits
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

variable {T : EvenTorus}


abbrev fkMedialBoundaryOrbitVisitCount
    (pairing : FKMedialLoopPairing T) (d e : FKMedialDart T) : Nat :=
  permOrbitVisitCount (fkMedialBoundaryStep pairing) d e


end
end StatMech.FrontierD

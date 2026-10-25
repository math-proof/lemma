/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopCriticalCycleCover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopThermodynamicLimit.Part3
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopCriticalCycleCover
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.Ising StatMech.FrontierA

noncomputable section

def ons_rectDualPathCriticalNormalizedCycleCoverTerm {M N : Nat}
    (embedding : KWStraightLineEmbedding (ons_rectDualGraph M N))
    (path : ons_RectDualPath M N)
    (sigma : Equiv.Perm (ons_rectDualGraph M N).Dart) : Complex :=
  ons_rectDualPathCriticalCycleCoverTerm embedding path sigma /
    ons_rectDualKWDet embedding ons_signedLoopCriticalWeight

end
end StatMech.Onsager

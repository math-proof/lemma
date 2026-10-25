/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopCriticalCycleCover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopThermodynamicLimit.Part3
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.Ising StatMech.FrontierA

noncomputable section

def ons_rectDualPathCriticalCycleCoverTerm {M N : Nat}
    (embedding : KWStraightLineEmbedding (ons_rectDualGraph M N))
    (path : ons_RectDualPath M N)
    (sigma : Equiv.Perm (ons_rectDualGraph M N).Dart) : Complex :=
  let matrix := 1 - kwGraphTransition (ons_rectDualGraph M N)
    (ons_rectDualPathDefectWeight path ons_signedLoopCriticalWeight)
    embedding.turnPhase
  (ons_signedLoopCriticalWeight : Complex) ^
      (2 * (ons_rectDualPathDefect path).card) *
    (((sigma.sign : Int) : Complex) *
      ∏ dart, matrix (sigma dart) dart)


end
end StatMech.Onsager

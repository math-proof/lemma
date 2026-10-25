/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopAnchoredCutInjective
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusWiredCut.Part5
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusDualRectangle.Part4
import Theorem.StatisticalMechanics.Code.Ising.KWDualBijection.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.BoxGraphPath.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStar.Part4
import Theorem.StatisticalMechanics.Code.FK.EdgeConfigZ.Part15
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusRectCutCycle.Part7
open Finset SimpleGraph
open scoped symmDiff


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.FrontierA StatMech.Walls

noncomputable section

noncomputable def ons_rectDualSpanningTree (M N : Nat) :
    SimpleGraph (ons_RectDualVertex M N) :=
  Classical.choose (ons_rectDualGraph_connected M N).exists_isTree_le

end
end StatMech.Onsager

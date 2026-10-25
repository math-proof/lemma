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
import Def.StatisticalMechanics.Code.Onsager.SignedLoopPlusRectCutCycle.Part8
open Finset SimpleGraph
open scoped symmDiff


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.FrontierA StatMech.Walls

noncomputable section

theorem ons_rectDualSpanningTree_le (M N : Nat) :
    ons_rectDualSpanningTree M N ≤ ons_rectDualGraph M N :=
  (Classical.choose_spec
    (ons_rectDualGraph_connected M N).exists_isTree_le).1

theorem ons_rectDualSpanningTree_isTree (M N : Nat) :
    (ons_rectDualSpanningTree M N).IsTree :=
  (Classical.choose_spec
    (ons_rectDualGraph_connected M N).exists_isTree_le).2

end
end StatMech.Onsager

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
import Def.StatisticalMechanics.Code.Onsager.SignedLoopPlusRectCutCycle.Part10
open Finset SimpleGraph
open scoped symmDiff


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.FrontierA StatMech.Walls

noncomputable section

theorem existsUnique_ons_plusRectDualCut_eq (n : Nat)
    (F : ons_PlusRectEvenSubgraph n) :
    ∃! config : AnchoredConfig (ons_PlusWiredVertex 2 n) none,
      ons_plusRectDualCut n config = F.1 := by
  let config := (ons_plusRectCutEvenEquiv n).symm F
  refine ⟨config, ?_, ?_⟩
  · exact congrArg Subtype.val
      ((ons_plusRectCutEvenEquiv n).apply_symm_apply F)
  · intro other hother
    apply ons_plusRectDualCut_injective n
    exact hother.trans (congrArg Subtype.val
      ((ons_plusRectCutEvenEquiv n).apply_symm_apply F)).symm


end
end StatMech.Onsager

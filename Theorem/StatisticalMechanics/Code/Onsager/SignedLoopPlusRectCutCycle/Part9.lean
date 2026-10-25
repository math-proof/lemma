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
import Instance.StatisticalMechanics.Code.Onsager.SignedLoopPlusRectCutCycle
open Finset SimpleGraph
open scoped symmDiff


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.FrontierA StatMech.Walls

noncomputable section

theorem ons_rectDualSpanningTree_complement_card (n : Nat) :
    ((ons_rectDualGraph (2 * n + 1) (2 * n + 1)).edgeFinset \
      (ons_rectDualSpanningTree (2 * n + 1) (2 * n + 1)).edgeFinset).card =
        (2 * n + 1) ^ 2 := by
  let k := 2 * n + 1
  let G := ons_rectDualGraph k k
  let T := ons_rectDualSpanningTree k k
  have hsub : T.edgeFinset ⊆ G.edgeFinset := by
    intro edge hedge
    induction edge using Sym2.inductionOn with
    | _ a b =>
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hedge ⊢
        exact ons_rectDualSpanningTree_le k k hedge
  have htree : T.edgeFinset.card + 1 = (k + 1) * (k + 1) := by
    calc
      T.edgeFinset.card + 1 =
          Fintype.card (ons_RectDualVertex k k) :=
        (ons_rectDualSpanningTree_isTree k k).card_edgeFinset
      _ = (k + 1) * (k + 1) := by simp [ons_RectDualVertex]
  have hedge : G.edgeFinset.card = 2 * k * (k + 1) := by
    rw [ons_rectDualGraph_card_edgeFinset]
    ring
  have hid : 2 * k * (k + 1) + 1 =
      (k + 1) * (k + 1) + k ^ 2 := by ring
  change (G.edgeFinset \ T.edgeFinset).card = k ^ 2
  rw [Finset.card_sdiff_of_subset hsub, hedge]
  omega


end
end StatMech.Onsager

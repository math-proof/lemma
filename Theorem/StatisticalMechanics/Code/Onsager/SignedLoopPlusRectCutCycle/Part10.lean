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
import Def.StatisticalMechanics.Code.Onsager.SignedLoopPlusRectCutCycle.Part9
open Finset SimpleGraph
open scoped symmDiff


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.FrontierA StatMech.Walls

noncomputable section

theorem ons_plusRectCutEven_injective (n : Nat) :
    Function.Injective (ons_plusRectCutEven n) := by
  intro config config' h
  apply ons_plusRectDualCut_injective n
  exact congrArg Subtype.val h

theorem card_ons_plusAnchoredConfig (n : Nat) :
    Fintype.card (AnchoredConfig (ons_PlusWiredVertex 2 n) none) =
      2 ^ ((2 * n + 1) ^ 2) := by
  calc
    Fintype.card (AnchoredConfig (ons_PlusWiredVertex 2 n) none) =
        Fintype.card ({x // x ∈ box 2 n} -> Bool) :=
      (Fintype.card_congr
        (ons_optionAnchoredEquiv
          (I := {x // x ∈ box 2 n}))).symm
    _ = 2 ^ Fintype.card {x // x ∈ box 2 n} := by
      rw [Fintype.card_fun]
      norm_num
    _ = 2 ^ ((2 * n + 1) ^ 2) := by
      rw [StatMech.FK.ecz_boxVerts_card]

theorem card_ons_plusRectEvenSubgraph_le (n : Nat) :
    Fintype.card (ons_PlusRectEvenSubgraph n) ≤
      2 ^ ((2 * n + 1) ^ 2) := by
  let G := ons_rectDualGraph (2 * n + 1) (2 * n + 1)
  let T := ons_rectDualSpanningTree (2 * n + 1) (2 * n + 1)
  have hbound := card_evenSubgraphs_le_spanningTree_complement G T
    (ons_rectDualSpanningTree_isTree
      (2 * n + 1) (2 * n + 1)).isAcyclic
  rw [ons_rectDualSpanningTree_complement_card] at hbound
  rw [show Fintype.card (ons_PlusRectEvenSubgraph n) =
      (evenSubgraphs
        (ons_rectDualGraph (2 * n + 1) (2 * n + 1))).card from
    Fintype.card_coe _]
  simpa [G] using hbound


theorem ons_plusRectCutEven_bijective (n : Nat) :
    Function.Bijective (ons_plusRectCutEven n) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨ons_plusRectCutEven_injective n, ?_⟩
  have hle := Fintype.card_le_of_injective
    (ons_plusRectCutEven n) (ons_plusRectCutEven_injective n)
  have hupper := card_ons_plusRectEvenSubgraph_le n
  rw [card_ons_plusAnchoredConfig] at hle ⊢
  omega

end
end StatMech.Onsager

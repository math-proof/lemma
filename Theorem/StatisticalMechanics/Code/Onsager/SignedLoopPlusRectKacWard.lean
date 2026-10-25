/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectKacWard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusRectCutCycle.Part12
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusWiredCutLimit
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularSpectralBridge.Part5
import Def.StatisticalMechanics.Code.Onsager.SignedLoopPlusRectKacWard
open scoped BigOperators
open Finset SimpleGraph MeasureTheory Filter Topology


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.FrontierA

noncomputable section

theorem card_ons_plusRectCutEven (n : Nat)
    (config : AnchoredConfig (ons_PlusWiredVertex 2 n) none) :
    (ons_plusRectCutEven n config).1.card =
      (multibondCut (ons_plusWiredBondEnds 2 n) config.1).card := by
  unfold ons_plusRectCutEven ons_plusRectDualCut
  rw [Finset.card_map]


theorem ons_plusWiredContourDenominator_eq_plusRectContourSum
    (n : Nat) (beta : Real) :
    ons_plusWiredContourDenominator 2 n beta =
      ons_plusRectContourSum n (Real.exp (-2 * beta)) := by
  unfold ons_plusWiredContourDenominator ons_plusRectContourSum
  rw [← (ons_plusRectCutEvenEquiv n).sum_comp]
  apply Finset.sum_congr rfl
  intro config _
  change Real.exp (-2 * beta) ^
      (multibondCut (ons_plusWiredBondEnds 2 n) config.1).card =
    Real.exp (-2 * beta) ^ (ons_plusRectCutEven n config).1.card
  rw [card_ons_plusRectCutEven]


theorem ons_plusWiredPathNumerator_eq_plusRectPathSum
    (n : Nat) (beta : Real) {u v : Site 2}
    (path : (hypercubicLattice 2).Walk u v) :
    ons_plusWiredPathNumerator 2 n beta u v =
      ons_plusRectPathSum n path (Real.exp (-2 * beta)) := by
  unfold ons_plusWiredPathNumerator ons_plusRectPathSum
  rw [← (ons_plusRectCutEvenEquiv n).sum_comp]
  apply Finset.sum_congr rfl
  intro config _
  change ons_plusWiredEndpointSign 2 n config.1 u v *
      Real.exp (-2 * beta) ^
        (multibondCut (ons_plusWiredBondEnds 2 n) config.1).card =
    ons_plusRectPathDefectSign n path (ons_plusRectCutEven n config) *
      Real.exp (-2 * beta) ^ (ons_plusRectCutEven n config).1.card
  rw [card_ons_plusRectCutEven]
  have hsign := ons_plusRectPathDefectSign_eq_endpointSign n
    (ons_plusRectCutEvenEquiv n config) path
  simpa using congrArg
    (fun sign : Real ↦ sign * Real.exp (-2 * beta) ^
      (multibondCut (ons_plusWiredBondEnds 2 n) config.1).card) hsign.symm


end
end StatMech.Onsager

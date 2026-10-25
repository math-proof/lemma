/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusWiredCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopAnchoredCut
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopLowTempPlus.Part3
import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
import Def.StatisticalMechanics.Code.Onsager.SignedLoopPlusWiredCut.Part3
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.FrontierA

noncomputable section

theorem ons_plusLowTempContourDenominator_eq_wired
    (d n : Nat) (beta : Real) :
    ons_plusLowTempContourDenominator d n beta =
      ons_plusWiredContourDenominator d n beta := by
  unfold ons_plusLowTempContourDenominator ons_plusWiredContourDenominator
  calc
    (∑ tau : {x // x ∈ box d n} → Bool,
      Real.exp (-2 * beta) ^
        (ons_fvCutEdges (bondFinsetTouch d n)
          (glue (plusField d) tau)).card) =
        ∑ tau : {x // x ∈ box d n} → Bool,
          Real.exp (-2 * beta) ^
            (multibondCut (ons_plusWiredBondEnds d n)
              (ons_optionAnchoredEquiv tau).1).card := by
      apply Finset.sum_congr rfl
      intro tau _
      rw [card_plusWiredCut_eq_fvCutEdges]
    _ = _ := optionInteriorCutSum_eq_anchored
      (ons_plusWiredBondEnds d n)
      (fun cut => Real.exp (-2 * beta) ^ cut.card)


end
end StatMech.Onsager

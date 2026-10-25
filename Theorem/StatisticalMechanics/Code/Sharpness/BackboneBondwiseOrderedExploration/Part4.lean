/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneBondwiseOrderedExploration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneExplorationSelector.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneOrderedDeterminedCut.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneActualSelectorSwitching.Part3
import Def.StatisticalMechanics.Code.Sharpness.BackboneBondwiseOrderedExploration.Part3
open Finset
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

namespace BackboneDeterminedCutSwitching

open FluxEdgeCopy

open BackboneLabeledSwitching

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

variable {D : Type*}

theorem fluxBitConfig_eq_on_freshSuffix
    (X : shb_DynamicEdgeExploration D (Sym2 V)) (d : D)
    (accepted : Sym2 V) (suffix : List (Sym2 V))
    (hfresh : SuffixFresh X d accepted suffix)
    (bit : Nat -> Bool) (m : G.edgeFinset -> Nat)
    (S T : Finset (FluxEdgeCopy.Copy G m))
    (hout : outsideCopies G m
      ((X.bondwiseOrdered.tests d).determinedCut accepted) S =
        outsideCopies G m
          ((X.bondwiseOrdered.tests d).determinedCut accepted) T) :
    ∀ e ∈ X.determinedTrace (X.advance d accepted) suffix,
      fluxBitConfig G bit (profileFlux G m S) e =
        fluxBitConfig G bit (profileFlux G m T) e := by
  intro e he
  have hecut := hfresh e he
  unfold fluxBitConfig
  split
  · rename_i hedge
    rw [profileFlux_eq_of_outsideCopies_eq G m _ S T hout ⟨e, hedge⟩ hecut]
  · rfl


end BackboneDeterminedCutSwitching
end StatMech.Sharpness

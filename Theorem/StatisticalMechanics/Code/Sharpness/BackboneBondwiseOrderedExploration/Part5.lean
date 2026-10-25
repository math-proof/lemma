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
import Instance.StatisticalMechanics.Code.Sharpness.BackboneBondwiseOrderedExploration.Part2
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

theorem bondwiseSuffixEvent_fluxEventOutsideCut
    (X : shb_DynamicEdgeExploration D (Sym2 V)) (d : D)
    (accepted : Sym2 V) (suffix : List (Sym2 V))
    (hfresh : SuffixFresh X d accepted suffix)
    (bit : Nat -> Bool) (m : G.edgeFinset -> Nat) :
    FluxEventOutsideCut G m
      ((X.bondwiseOrdered.tests d).determinedCut accepted)
      (BondwiseSuffixEvent G X (X.advance d accepted) suffix bit) := by
  intro S T hout
  apply X.selects_iff_of_agreeOn_determinedTrace
  exact fluxBitConfig_eq_on_freshSuffix G X d accepted suffix
    hfresh bit m S T hout


theorem rawFiberMass_eq_of_bondwiseDeterminedToggle
    (X : shb_DynamicEdgeExploration D (Sym2 V)) (d : D)
    (accepted : Sym2 V)
    (beta : Real) (J : Sym2 V -> Real)
    (m : G.edgeFinset -> Nat) (A C : Finset V)
    (P : Finset (FluxEdgeCopy.Copy G m))
    (hPsrc : RandomCurrent.sources (endsM G m) P = C)
    (hPcut : SupportedInCut G m
      ((X.bondwiseOrdered.tests d).determinedCut accepted) P)
    (Q : (G.edgeFinset -> Nat) -> Prop) [DecidablePred Q]
    (hQ : FluxEventOutsideCut G m
      ((X.bondwiseOrdered.tests d).determinedCut accepted) Q) :
    rawFiberMass G beta J m A Q =
      rawFiberMass G beta J m (A ∆ C) Q :=
  rawFiberMass_eq_of_orderedDeterminedToggle G
    (X.bondwiseOrdered.tests d) accepted beta J m A C P hPsrc hPcut Q hQ


theorem rawFiberMass_eq_of_bondwiseSuffixToggle
    (X : shb_DynamicEdgeExploration D (Sym2 V)) (d : D)
    (accepted : Sym2 V) (suffix : List (Sym2 V))
    (hfresh : SuffixFresh X d accepted suffix)
    (bit : Nat -> Bool)
    (beta : Real) (J : Sym2 V -> Real)
    (m : G.edgeFinset -> Nat) (A C : Finset V)
    (P : Finset (FluxEdgeCopy.Copy G m))
    (hPsrc : RandomCurrent.sources (endsM G m) P = C)
    (hPcut : SupportedInCut G m
      ((X.bondwiseOrdered.tests d).determinedCut accepted) P) :
    rawFiberMass G beta J m A
        (BondwiseSuffixEvent G X (X.advance d accepted) suffix bit) =
      rawFiberMass G beta J m (A ∆ C)
        (BondwiseSuffixEvent G X (X.advance d accepted) suffix bit) := by
  apply rawFiberMass_eq_of_bondwiseDeterminedToggle G X d accepted
    beta J m A C P hPsrc hPcut
  exact bondwiseSuffixEvent_fluxEventOutsideCut G X d accepted suffix
    hfresh bit m


end BackboneDeterminedCutSwitching
end StatMech.Sharpness

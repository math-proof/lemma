/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneActualSelectorSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneExplorationSelectorAdmissible.Part3
import Abbrev.StatisticalMechanics.Code.Sharpness.BackboneActualSelectorSwitching
open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

noncomputable def shb_selectorSwitchLeftTerm
    (S : shb_CurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V))
    (mr : shb_SelectorSwitchPair d s) : Real :=
  if S.Fiber d (s :: ss) mr.1 /\
      sources (shb_BackboneExplorationDomain.advance d s).graph
        (ofEdgeFun (shb_BackboneExplorationDomain.advance d s).graph mr.2) = ∅
  then
    shb_explorationCoordinateWeight beta J d mr.1 *
      shb_explorationCoordinateWeight beta J
        (shb_BackboneExplorationDomain.advance d s) mr.2
  else 0


noncomputable def shb_selectorSwitchRightTerm
    (S : shb_CurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (mr : shb_SelectorSwitchPair d s) : Real :=
  if shb_ActiveSegmentFiber d s hs mr.1 /\
      S.Fiber (shb_BackboneExplorationDomain.advance d s) ss mr.2
  then
    shb_explorationCoordinateWeight beta J d mr.1 *
      shb_explorationCoordinateWeight beta J
        (shb_BackboneExplorationDomain.advance d s) mr.2
  else 0


def shb_CurrentDynamicSelector.SwitchingLaw
    (S : shb_CurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real) : Prop :=
  forall d s ss (hs : s ∈ d.active),
    exists switch : shb_SelectorSwitchPair d s ≃ shb_SelectorSwitchPair d s,
      forall mr,
        shb_selectorSwitchLeftTerm S beta J d s ss mr =
          shb_selectorSwitchRightTerm S beta J d s ss hs (switch mr)


end
end StatMech.Sharpness

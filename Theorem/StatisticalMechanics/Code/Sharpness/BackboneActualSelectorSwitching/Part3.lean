/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneActualSelectorSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneExplorationSelectorAdmissible.Part3
import Def.StatisticalMechanics.Code.Sharpness.BackboneActualSelectorSwitching.Part4
open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

theorem shb_currentDynamicSelector_actualMass_nil
    (S : shb_CurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real) (d : shb_ExplorationDomain V) :
    S.actualMass beta J d [] = currentSum d.graph beta J ∅ := by
  unfold shb_CurrentDynamicSelector.actualMass
    shb_actualExplorationFiberMass currentSum
  apply tsum_congr
  intro m
  have hiff :
      (sources d.graph (ofEdgeFun d.graph m) = S.sourceClass d [] /\
          S.select d m = []) <->
        sources d.graph (ofEdgeFun d.graph m) = ∅ := by
    rw [S.sourceClass_nil d]
    constructor
    · exact And.left
    · intro h
      exact ⟨h, S.select_nil_of_sources_empty d m h⟩
  by_cases h : sources d.graph (ofEdgeFun d.graph m) = ∅
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun hh => h (hiff.mp hh)), if_neg h]


theorem shb_currentDynamicSelector_actualMass_inactive
    (S : shb_CurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∉ d.active) :
    S.actualMass beta J d (s :: ss) = 0 := by
  unfold shb_CurrentDynamicSelector.actualMass
    shb_actualExplorationFiberMass
  rw [show (fun m : d.graph.edgeFinset -> Nat =>
      if sources d.graph (ofEdgeFun d.graph m) = S.sourceClass d (s :: ss) /\
          S.select d m = s :: ss then
        weight d.graph beta J (ofEdgeFun d.graph m) else 0) =
      (fun _ => 0) by
    funext m
    rw [if_neg]
    intro h
    exact S.select_ne_cons_of_not_active d s ss m hs h.2]
  exact tsum_zero


theorem shb_currentDynamicSelector_actualMass_active
    (S : shb_CurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (hswitch : S.SwitchingLaw beta J)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active) :
    S.actualMass beta J d (s :: ss) *
        currentSum (shb_BackboneExplorationDomain.advance d s).graph
          beta J ∅ =
      shb_segmentNum beta J d s *
        S.actualMass beta J
          (shb_BackboneExplorationDomain.advance d s) ss := by
  let d' := shb_BackboneExplorationDomain.advance d s
  obtain ⟨switch, hswitchTerm⟩ := hswitch d s ss hs
  have hfull : Summable (fun m : d.graph.edgeFinset -> Nat =>
      if S.Fiber d (s :: ss) m then
        shb_explorationCoordinateWeight beta J d m else 0) :=
    shb_summable_explorationFiberIndicator beta J d _
  have hvac : Summable (fun r : d'.graph.edgeFinset -> Nat =>
      if sources d'.graph (ofEdgeFun d'.graph r) = ∅ then
        shb_explorationCoordinateWeight beta J d' r else 0) :=
    shb_summable_explorationFiberIndicator beta J d' _
  have hstep : Summable (fun m : d.graph.edgeFinset -> Nat =>
      if shb_ActiveSegmentFiber d s hs m then
        shb_explorationCoordinateWeight beta J d m else 0) :=
    shb_summable_explorationFiberIndicator beta J d _
  have hsuffix : Summable (fun r : d'.graph.edgeFinset -> Nat =>
      if S.Fiber d' ss r then
        shb_explorationCoordinateWeight beta J d' r else 0) :=
    shb_summable_explorationFiberIndicator beta J d' _
  have hleft :
      (∑' mr : shb_SelectorSwitchPair d s,
          shb_selectorSwitchLeftTerm S beta J d s ss mr) =
        S.actualMass beta J d (s :: ss) * currentSum d'.graph beta J ∅ := by
    rw [show (∑' mr : shb_SelectorSwitchPair d s,
        shb_selectorSwitchLeftTerm S beta J d s ss mr) =
      (∑' mr : (d.graph.edgeFinset -> Nat) × (d'.graph.edgeFinset -> Nat),
        (if S.Fiber d (s :: ss) mr.1 then
            shb_explorationCoordinateWeight beta J d mr.1 else 0) *
          (if sources d'.graph (ofEdgeFun d'.graph mr.2) = ∅ then
            shb_explorationCoordinateWeight beta J d' mr.2 else 0)) by
      apply tsum_congr
      intro mr
      unfold shb_selectorSwitchLeftTerm
      by_cases h₁ : S.Fiber d (s :: ss) mr.1 <;>
        by_cases h₂ : sources d'.graph (ofEdgeFun d'.graph mr.2) = ∅ <;>
        simp [h₁, h₂, d']]
    rw [shb_tsum_prod_factor _ _ hfull hvac]
    unfold shb_explorationCoordinateWeight
    rw [← S.actualMass_eq_fiberTsum beta J d (s :: ss)]
    unfold currentSum
    rfl
  have hright :
      (∑' mr : shb_SelectorSwitchPair d s,
          shb_selectorSwitchRightTerm S beta J d s ss hs mr) =
        shb_segmentNum beta J d s * S.actualMass beta J d' ss := by
    rw [show (∑' mr : shb_SelectorSwitchPair d s,
        shb_selectorSwitchRightTerm S beta J d s ss hs mr) =
      (∑' mr : (d.graph.edgeFinset -> Nat) × (d'.graph.edgeFinset -> Nat),
        (if shb_ActiveSegmentFiber d s hs mr.1 then
            shb_explorationCoordinateWeight beta J d mr.1 else 0) *
          (if S.Fiber d' ss mr.2 then
            shb_explorationCoordinateWeight beta J d' mr.2 else 0)) by
      apply tsum_congr
      intro mr
      unfold shb_selectorSwitchRightTerm
      by_cases h₁ : shb_ActiveSegmentFiber d s hs mr.1 <;>
        by_cases h₂ : S.Fiber d' ss mr.2 <;> simp [h₁, h₂, d']]
    rw [shb_tsum_prod_factor _ _ hstep hsuffix,
      shb_activeSegmentFiberMass_eq_segmentNum beta J d s hs]
    unfold shb_explorationCoordinateWeight
    rw [← S.actualMass_eq_fiberTsum beta J d' ss]
  rw [← hleft, ← hright]
  calc
    (∑' mr : shb_SelectorSwitchPair d s,
        shb_selectorSwitchLeftTerm S beta J d s ss mr) =
        ∑' mr : shb_SelectorSwitchPair d s,
          shb_selectorSwitchRightTerm S beta J d s ss hs (switch mr) :=
      tsum_congr hswitchTerm
    _ = ∑' mr : shb_SelectorSwitchPair d s,
          shb_selectorSwitchRightTerm S beta J d s ss hs mr :=
      switch.tsum_eq _


theorem shb_CurrentDynamicSelector.actualFiberRealizes
    (S : shb_CurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (hswitch : S.SwitchingLaw beta J) :
    shb_ActualExplorationFiberRealizes beta J (S.actualMass beta J) := by
  refine ⟨shb_currentDynamicSelector_actualMass_nil S beta J, ?_, ?_⟩
  · intro d s ss hs
    exact shb_currentDynamicSelector_actualMass_active S beta J
      hswitch d s ss hs
  · intro d s ss hs
    exact shb_currentDynamicSelector_actualMass_inactive S beta J d s ss hs


theorem shb_CurrentDynamicSelector.actualMass_eq_generated
    (S : shb_CurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (hswitch : S.SwitchingLaw beta J) :
    S.actualMass beta J = shb_generatedExplorationFiberMass beta J := by
  exact shb_actualExplorationFiberMass_eq_generated beta J S.sourceClass
    (fun d word m => S.select d m = word)
    (S.actualFiberRealizes beta J hswitch)

end
end StatMech.Sharpness

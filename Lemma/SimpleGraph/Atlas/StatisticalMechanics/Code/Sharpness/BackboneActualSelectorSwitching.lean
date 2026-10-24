import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.BackboneActualSelectorSwitching
open SimpleGraph Finset StatMech StatMech.Sharpness


/--
[shb_CurrentDynamicSelector.actualMass_eq_fiberTsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneActualSelectorSwitching.lean)
-/
@[path]
private lemma actualMass_eq_fiberTsum_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {word : List (shb_ExplorationSegment V)}
-- given
  (S : shb_CurrentDynamicSelector (V := V))
  (J : Sym2 V -> Real) :
-- imply
  S.actualMass beta J d word = ∑' m : d.graph.edgeFinset -> Nat, if S.Fiber d word m then weight d.graph beta J (ofEdgeFun d.graph m) else 0 := by
-- proof
  apply StatMech.Sharpness.shb_CurrentDynamicSelector.actualMass_eq_fiberTsum S beta J d word

/--
[shb_summable_explorationFiberIndicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneActualSelectorSwitching.lean)
-/
@[path]
private lemma shb_summable_explorationFiberIndicator_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {beta : Real}
  {d : shb_ExplorationDomain V}
  [DecidablePred P]
-- given
  (J : Sym2 V -> Real)
  (P : (d.graph.edgeFinset -> Nat) -> Prop) :
-- imply
  Summable (fun m => if P m then shb_explorationCoordinateWeight beta J d m else 0) := by
-- proof
  apply StatMech.Sharpness.shb_summable_explorationFiberIndicator beta J d P

/--
[shb_activeSegmentFiberMass_eq_segmentNum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneActualSelectorSwitching.lean)
-/
@[path]
private lemma shb_activeSegmentFiberMass_eq_segmentNum_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
-- given
  (J : Sym2 V -> Real)
  (hs : s ∈ d.active) :
-- imply
  (∑' m : d.graph.edgeFinset -> Nat, if shb_ActiveSegmentFiber d s hs m then shb_explorationCoordinateWeight beta J d m else 0) = shb_segmentNum beta J d s := by
-- proof
  apply StatMech.Sharpness.shb_activeSegmentFiberMass_eq_segmentNum beta J d s hs

/--
[shb_currentDynamicSelector_actualMass_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneActualSelectorSwitching.lean)
-/
@[path]
private lemma shb_currentDynamicSelector_actualMass_nil_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {beta : Real}
  {d : shb_ExplorationDomain V}
-- given
  (S : shb_CurrentDynamicSelector (V := V))
  (J : Sym2 V -> Real) :
-- imply
  S.actualMass beta J d [] = currentSum d.graph beta J ∅ := by
-- proof
  apply StatMech.Sharpness.shb_currentDynamicSelector_actualMass_nil S beta J d

/--
[shb_currentDynamicSelector_actualMass_inactive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneActualSelectorSwitching.lean)
-/
@[path]
private lemma shb_currentDynamicSelector_actualMass_inactive_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
  {ss : List (shb_ExplorationSegment V)}
-- given
  (S : shb_CurrentDynamicSelector (V := V))
  (J : Sym2 V -> Real)
  (hs : s ∉ d.active) :
-- imply
  S.actualMass beta J d (s :: ss) = 0 := by
-- proof
  apply StatMech.Sharpness.shb_currentDynamicSelector_actualMass_inactive S beta J d s ss hs

/--
[shb_currentDynamicSelector_actualMass_active](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneActualSelectorSwitching.lean)
-/
@[path]
private lemma shb_currentDynamicSelector_actualMass_active_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
  {ss : List (shb_ExplorationSegment V)}
-- given
  (S : shb_CurrentDynamicSelector (V := V))
  (J : Sym2 V -> Real)
  (hswitch : S.SwitchingLaw beta J)
  (hs : s ∈ d.active) :
-- imply
  S.actualMass beta J d (s :: ss) * currentSum (shb_BackboneExplorationDomain.advance d s).graph beta J ∅ = shb_segmentNum beta J d s * S.actualMass beta J (shb_BackboneExplorationDomain.advance d s) ss := by
-- proof
  apply StatMech.Sharpness.shb_currentDynamicSelector_actualMass_active S beta J hswitch d s ss hs

/--
[shb_CurrentDynamicSelector.actualFiberRealizes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneActualSelectorSwitching.lean)
-/
@[path]
private lemma actualFiberRealizes_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {beta : Real}
-- given
  (S : shb_CurrentDynamicSelector (V := V))
  (J : Sym2 V -> Real)
  (hswitch : S.SwitchingLaw beta J) :
-- imply
  shb_ActualExplorationFiberRealizes beta J (S.actualMass beta J) := by
-- proof
  apply StatMech.Sharpness.shb_CurrentDynamicSelector.actualFiberRealizes S beta J hswitch

/--
[shb_CurrentDynamicSelector.actualMass_eq_generated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneActualSelectorSwitching.lean)
-/
@[path]
private lemma actualMass_eq_generated_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {beta : Real}
-- given
  (S : shb_CurrentDynamicSelector (V := V))
  (J : Sym2 V -> Real)
  (hswitch : S.SwitchingLaw beta J) :
-- imply
  S.actualMass beta J = shb_generatedExplorationFiberMass beta J := by
-- proof
  apply StatMech.Sharpness.shb_CurrentDynamicSelector.actualMass_eq_generated S beta J hswitch


-- created on 2026-10-23

import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.BackboneMultiStepP2
open SimpleGraph Finset StatMech StatMech.Sharpness StatMech.Sharpness.BackboneMultiStepBondProgram


/--
[designatedHead_unrestricted_cut_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneMultiStepP2.lean)
-/
@[path]
private lemma designatedHead_unrestricted_cut_factor_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {e : d.graph.edgeFinset}
-- given
  (J : Sym2 V -> Real) :
-- imply
  shb_fullWeightMass d.graph beta J = shb_cutLeftMass d.graph beta J (fun g => g.1 = e.1) * shb_cutRightMass d.graph beta J (fun g => g.1 = e.1) := by
-- proof
  apply StatMech.Sharpness.BackboneMultiStepBondProgram.designatedHead_unrestricted_cut_factor beta J d e

/--
[selectorSpec_not_fiber_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneMultiStepP2.lean)
-/
@[path]
private lemma selectorSpec_not_fiber_singleton_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
-- given
  (m : d.graph.edgeFinset -> Nat) :
-- imply
  ¬((selectorSpec (V := V)).toPartialSelector).Fiber d [s] m := by
-- proof
  apply StatMech.Sharpness.BackboneMultiStepBondProgram.selectorSpec_not_fiber_singleton d s m

/--
[selectorSpec_actualMass_singleton_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneMultiStepP2.lean)
-/
@[path]
private lemma selectorSpec_actualMass_singleton_eq_zero_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  ((selectorSpec (V := V)).toPartialSelector).actualMass beta J d [s] = 0 := by
-- proof
  apply StatMech.Sharpness.BackboneMultiStepBondProgram.selectorSpec_actualMass_singleton_eq_zero beta J d s

/--
[selectorSpec_pair_clearedP2_of_toggleExists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneMultiStepP2.lean)
-/
@[path]
private lemma selectorSpec_pair_clearedP2_of_toggleExists_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (J : Sym2 V -> Real)
  (heactive : canonicalEdgeSegment d.graph e ∈ d.active)
  (htoggle : (selectorSpec (V := V)).CanonicalBondwiseToggleExists beta J d (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f] heactive) :
-- imply
  ((selectorSpec (V := V)).toPartialSelector).actualMass beta J d [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f] * currentSum (shb_BackboneExplorationDomain.advance d (canonicalEdgeSegment d.graph e)).graph beta J ∅ = shb_segmentNum beta J d (canonicalEdgeSegment d.graph e) * ((selectorSpec (V := V)).toPartialSelector).actualMass beta J (shb_BackboneExplorationDomain.advance d (canonicalEdgeSegment d.graph e)) [canonicalEdgeSegment d.graph f] := by
-- proof
  apply StatMech.Sharpness.BackboneMultiStepBondProgram.selectorSpec_pair_clearedP2_of_toggleExists beta J d e f heactive htoggle

/--
[selectorSpec_pair_clearedMass_eq_zero_of_toggleExists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneMultiStepP2.lean)
-/
@[path]
private lemma selectorSpec_pair_clearedMass_eq_zero_of_toggleExists_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (J : Sym2 V -> Real)
  (heactive : canonicalEdgeSegment d.graph e ∈ d.active)
  (htoggle : (selectorSpec (V := V)).CanonicalBondwiseToggleExists beta J d (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f] heactive) :
-- imply
  ((selectorSpec (V := V)).toPartialSelector).actualMass beta J d [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f] * currentSum (shb_BackboneExplorationDomain.advance d (canonicalEdgeSegment d.graph e)).graph beta J ∅ = 0 := by
-- proof
  apply StatMech.Sharpness.BackboneMultiStepBondProgram.selectorSpec_pair_clearedMass_eq_zero_of_toggleExists beta J d e f heactive htoggle

/--
[selectorSpec_not_admissible_unitFlux_of_active_eq_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneMultiStepP2.lean)
-/
@[path]
private lemma selectorSpec_not_admissible_unitFlux_of_active_eq_empty_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e : d.graph.edgeFinset}
-- given
  (hactive : d.active = ∅) :
-- imply
  ¬((selectorSpec (V := V)).toPartialSelector.Admissible d (unitFlux d.graph e)) := by
-- proof
  apply StatMech.Sharpness.BackboneMultiStepBondProgram.selectorSpec_not_admissible_unitFlux_of_active_eq_empty d e hactive

/--
[weight_twoUnitFlux_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneMultiStepP2.lean)
-/
@[path]
private lemma weight_twoUnitFlux_pos_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 < beta)
  (hJ : ∀ g, 0 < J g) :
-- imply
  0 < weight d.graph beta J (ofEdgeFun d.graph (twoUnitFlux d.graph e f)) := by
-- proof
  apply StatMech.Sharpness.BackboneMultiStepBondProgram.weight_twoUnitFlux_pos beta J hbeta hJ d e f

/--
[selectorSpec_actualMass_designated_pair_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneMultiStepP2.lean)
-/
@[path]
private lemma selectorSpec_actualMass_designated_pair_pos_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 < beta)
  (hJ : ∀ g, 0 < J g)
  (hpair : IsDesignatedPair d e f)
  (heactive : canonicalEdgeSegment d.graph e ∈ d.active)
  (hfactive : canonicalEdgeSegment d.graph f ∈ d.active) :
-- imply
  0 < ((selectorSpec (V := V)).toPartialSelector).actualMass beta J d [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f] := by
-- proof
  apply StatMech.Sharpness.BackboneMultiStepBondProgram.selectorSpec_actualMass_designated_pair_pos beta J hbeta hJ d e f hpair heactive hfactive

/--
[selectorSpec_not_pair_toggleExists_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneMultiStepP2.lean)
-/
@[path]
private lemma selectorSpec_not_pair_toggleExists_of_pos_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 < beta)
  (hJ : ∀ g, 0 < J g)
  (hpair : IsDesignatedPair d e f)
  (heactive : canonicalEdgeSegment d.graph e ∈ d.active)
  (hfactive : canonicalEdgeSegment d.graph f ∈ d.active) :
-- imply
  ¬ (selectorSpec (V := V)).CanonicalBondwiseToggleExists beta J d (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f] heactive := by
-- proof
  apply StatMech.Sharpness.BackboneMultiStepBondProgram.selectorSpec_not_pair_toggleExists_of_pos beta J hbeta hJ d e f hpair heactive hfactive


-- created on 2026-10-23

import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedPhysicalKeyCounterexample.Part4
open StatMech StatMech.FrontierD


/--
[sixVertexFourByTwo_locallyDegreeTwo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedPhysicalKeyCounterexample.lean)
-/
@[path]
private lemma sixVertexFourByTwo_locallyDegreeTwo_eq :
-- imply
  SixVertexLocallyDegreeTwo sixVertexFourByTwoLowArrows sixVertexFourByTwoHighArrows := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwo_locallyDegreeTwo

/--
[sixVertexFourByTwoAlignedPairings_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedPhysicalKeyCounterexample.lean)
-/
@[path]
private lemma sixVertexFourByTwoAlignedPairings_false_eq
  {d : SixVertexOrientedDisagreementDart sixVertexFourByTwoLowArrows sixVertexFourByTwoHighArrows} :
-- imply
  let retie := orientedDartAlignedRetie sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice sixVertexFourByTwo_locallyDegreeTwo d retie.pairingP = false ∧ retie.pairingQ = false := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoAlignedPairings_false d

/--
[sixVertexFourByTwoAlignedRoutingPairing_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedPhysicalKeyCounterexample.lean)
-/
@[path]
private lemma sixVertexFourByTwoAlignedRoutingPairing_false_eq
  {layer : Bool}
  {v : sixVertexFourByTwoTorus.Vertex} :
-- imply
  alignedRoutingPairing sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice sixVertexFourByTwo_locallyDegreeTwo layer v = false := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoAlignedRoutingPairing_false layer v

/--
[sixVertexFourByTwoAlignedRoutingPairing_false_funext](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedPhysicalKeyCounterexample.lean)
-/
@[path]
private lemma sixVertexFourByTwoAlignedRoutingPairing_false_funext_eq
  {layer : Bool} :
-- imply
  alignedRoutingPairing sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice sixVertexFourByTwo_locallyDegreeTwo layer = fun _ => false := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoAlignedRoutingPairing_false_funext layer

/--
[finiteFirstReturn_eq_step_of_selected_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedPhysicalKeyCounterexample.lean)
-/
@[path]
private lemma finiteFirstReturn_eq_step_of_selected_step_eq
  [Fintype A]
  [DecidableEq A]
  {sigma : Equiv.Perm A}
  [DecidablePred selected]
  {x : {a : A // selected a}}
-- given
  (selected : A → Prop)
  (hstep : selected (sigma x.1)) :
-- imply
  (finiteFirstReturn sigma selected x).1 = sigma x.1 := by
-- proof
  apply StatMech.FrontierD.finiteFirstReturn_eq_step_of_selected_step sigma selected x hstep

/--
[doubledAlignedFirstReturnPerm_eq_of_boundary_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedPhysicalKeyCounterexample.lean)
-/
@[path]
private lemma doubledAlignedFirstReturnPerm_eq_of_boundary_step_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {x y : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hstep : alignedBoundaryPerm homega heta hdegree false (doubledAlignedBlackDart homega heta hdegree false x) = doubledAlignedBlackDart homega heta hdegree false y) :
-- imply
  doubledAlignedFirstReturnPerm homega heta hdegree x = y := by
-- proof
  apply StatMech.FrontierD.doubledAlignedFirstReturnPerm_eq_of_boundary_step homega heta hdegree x y hstep

/--
[sixVertexFourByTwoAlignedBoundary_seed_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedPhysicalKeyCounterexample.lean)
-/
@[path]
private lemma sixVertexFourByTwoAlignedBoundary_seed_step_eq
  {branch : Bool} :
-- imply
  alignedBoundaryPerm sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice sixVertexFourByTwo_locallyDegreeTwo false (doubledAlignedBlackDart sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice sixVertexFourByTwo_locallyDegreeTwo false (sixVertexFourByTwoOrientedSeed, branch)) = doubledAlignedBlackDart sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice sixVertexFourByTwo_locallyDegreeTwo false (sixVertexFourByTwoOrientedNorthSeed, branch) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoAlignedBoundary_seed_step branch

/--
[sixVertexFourByTwoAlignedBoundary_east_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedPhysicalKeyCounterexample.lean)
-/
@[path]
private lemma sixVertexFourByTwoAlignedBoundary_east_step_eq :
-- imply
  alignedBoundaryPerm sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice sixVertexFourByTwo_locallyDegreeTwo false (doubledAlignedBlackDart sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice sixVertexFourByTwo_locallyDegreeTwo false (sixVertexFourByTwoOrientedEastSeed, false)) = doubledAlignedBlackDart sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice sixVertexFourByTwo_locallyDegreeTwo false (sixVertexFourByTwoOrientedSeed, false) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoAlignedBoundary_east_step

/--
[sixVertexFourByTwoFirstReturn_seed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedPhysicalKeyCounterexample.lean)
-/
@[path]
private lemma sixVertexFourByTwoFirstReturn_seed_eq
  {branch : Bool} :
-- imply
  doubledAlignedFirstReturnPerm sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice sixVertexFourByTwo_locallyDegreeTwo (sixVertexFourByTwoOrientedSeed, branch) = (sixVertexFourByTwoOrientedNorthSeed, branch) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoFirstReturn_seed branch

/--
[sixVertexFourByTwoFirstReturn_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedPhysicalKeyCounterexample.lean)
-/
@[path]
private lemma sixVertexFourByTwoFirstReturn_east_eq :
-- imply
  doubledAlignedFirstReturnPerm sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice sixVertexFourByTwo_locallyDegreeTwo (sixVertexFourByTwoOrientedEastSeed, false) = (sixVertexFourByTwoOrientedSeed, false) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoFirstReturn_east

/--
[sixVertexFourByTwoBranchPredecessor_eq_seed_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedPhysicalKeyCounterexample.lean)
-/
@[path]
private lemma sixVertexFourByTwoBranchPredecessor_eq_seed_iff_eq
  {branch : Bool}
  {d : SixVertexOrientedDisagreementDart sixVertexFourByTwoLowArrows sixVertexFourByTwoHighArrows} :
-- imply
  sixVertexDegreeTwoBranchPredecessor sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice sixVertexFourByTwo_locallyDegreeTwo branch d = sixVertexFourByTwoOrientedSeed ↔ d = sixVertexFourByTwoOrientedNorthSeed := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoBranchPredecessor_eq_seed_iff branch d

/--
[sixVertexFourByTwoSynchronizedSeed_isIsolated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedPhysicalKeyCounterexample.lean)
-/
@[path]
private lemma sixVertexFourByTwoSynchronizedSeed_isIsolated_eq :
-- imply
  (sixVertexDegreeTwoSynchronizedGraph sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice sixVertexFourByTwo_locallyDegreeTwo).IsIsolated sixVertexFourByTwoOrientedSeed := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoSynchronizedSeed_isIsolated

/--
[sixVertexFourByTwoSynchronizedComponentSelector_eq_true_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedPhysicalKeyCounterexample.lean)
-/
@[path]
private lemma sixVertexFourByTwoSynchronizedComponentSelector_eq_true_iff_eq
  {d : SixVertexOrientedDisagreementDart sixVertexFourByTwoLowArrows sixVertexFourByTwoHighArrows} :
-- imply
  sixVertexDegreeTwoSynchronizedComponentSelector sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice sixVertexFourByTwo_locallyDegreeTwo sixVertexFourByTwoSynchronizedSeedComponent d = true ↔ d = sixVertexFourByTwoOrientedSeed := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoSynchronizedComponentSelector_eq_true_iff d

/--
[sixVertexFourByTwoSynchronizedSeedComponent_charge_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedPhysicalKeyCounterexample.lean)
-/
@[path]
private lemma sixVertexFourByTwoSynchronizedSeedComponent_charge_one_eq :
-- imply
  sixVertexDegreeTwoSynchronizedComponentCharge sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice sixVertexFourByTwo_locallyDegreeTwo sixVertexFourByTwoSynchronizedSeedComponent = 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoSynchronizedSeedComponent_charge_one

/--
[sixVertexFourByTwoSynchronizedSelector_seed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedPhysicalKeyCounterexample.lean)
-/
@[path]
private lemma sixVertexFourByTwoSynchronizedSelector_seed_eq :
-- imply
  sixVertexDegreeTwoSynchronizedComponentDoubledSelector sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice sixVertexFourByTwo_locallyDegreeTwo sixVertexFourByTwoSynchronizedSeedComponent (sixVertexFourByTwoOrientedSeed, false) = true := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoSynchronizedSelector_seed

/--
[sixVertexFourByTwoSynchronizedSelector_seed_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedPhysicalKeyCounterexample.lean)
-/
@[path]
private lemma sixVertexFourByTwoSynchronizedSelector_seed_true_eq :
-- imply
  sixVertexDegreeTwoSynchronizedComponentDoubledSelector sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice sixVertexFourByTwo_locallyDegreeTwo sixVertexFourByTwoSynchronizedSeedComponent (sixVertexFourByTwoOrientedSeed, true) = true := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoSynchronizedSelector_seed_true

/--
[sixVertexFourByTwoSynchronizedSelector_north](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedPhysicalKeyCounterexample.lean)
-/
@[path]
private lemma sixVertexFourByTwoSynchronizedSelector_north_eq
  {branch : Bool} :
-- imply
  sixVertexDegreeTwoSynchronizedComponentDoubledSelector sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice sixVertexFourByTwo_locallyDegreeTwo sixVertexFourByTwoSynchronizedSeedComponent (sixVertexFourByTwoOrientedNorthSeed, branch) = false := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoSynchronizedSelector_north branch

/--
[sixVertexFourByTwoSynchronizedSelector_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedPhysicalKeyCounterexample.lean)
-/
@[path]
private lemma sixVertexFourByTwoSynchronizedSelector_east_eq :
-- imply
  sixVertexDegreeTwoSynchronizedComponentDoubledSelector sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice sixVertexFourByTwo_locallyDegreeTwo sixVertexFourByTwoSynchronizedSeedComponent (sixVertexFourByTwoOrientedEastSeed, false) = false := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoSynchronizedSelector_east

/--
[sixVertexFourByTwoTransition_seed_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedPhysicalKeyCounterexample.lean)
-/
@[path]
private lemma sixVertexFourByTwoTransition_seed_false_eq :
-- imply
  sixVertexDegreeTwoSynchronizedComponentTransitionBit sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice sixVertexFourByTwo_locallyDegreeTwo sixVertexFourByTwoSynchronizedSeedComponent (sixVertexFourByTwoOrientedSeed, false) = true := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoTransition_seed_false

/--
[sixVertexFourByTwoTransition_north_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedPhysicalKeyCounterexample.lean)
-/
@[path]
private lemma sixVertexFourByTwoTransition_north_true_eq :
-- imply
  sixVertexDegreeTwoSynchronizedComponentTransitionBit sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice sixVertexFourByTwo_locallyDegreeTwo sixVertexFourByTwoSynchronizedSeedComponent (sixVertexFourByTwoOrientedNorthSeed, true) = true := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoTransition_north_true

/--
[sixVertexFourByTwoPhysicalRetieMask_seed_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedPhysicalKeyCounterexample.lean)
-/
@[path]
private lemma sixVertexFourByTwoPhysicalRetieMask_seed_false_eq :
-- imply
  sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice sixVertexFourByTwo_locallyDegreeTwo sixVertexFourByTwoSynchronizedSeedComponent false (doubledAlignedVertex (sixVertexFourByTwoOrientedSeed, false)) = true := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoPhysicalRetieMask_seed_false

/--
[sixVertexFourByTwoPhysicalRetieMask_north_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedPhysicalKeyCounterexample.lean)
-/
@[path]
private lemma sixVertexFourByTwoPhysicalRetieMask_north_true_eq :
-- imply
  sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice sixVertexFourByTwo_locallyDegreeTwo sixVertexFourByTwoSynchronizedSeedComponent false (doubledAlignedVertex (sixVertexFourByTwoOrientedNorthSeed, true)) = true := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoPhysicalRetieMask_north_true

/--
[sixVertexFourByTwoParity_seed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedPhysicalKeyCounterexample.lean)
-/
@[path]
private lemma sixVertexFourByTwoParity_seed_eq :
-- imply
  fkMedialVertexParity (doubledAlignedVertex (sixVertexFourByTwoOrientedSeed, false)) = false := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoParity_seed

/--
[sixVertexFourByTwoParity_north](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedPhysicalKeyCounterexample.lean)
-/
@[path]
private lemma sixVertexFourByTwoParity_north_eq :
-- imply
  fkMedialVertexParity (doubledAlignedVertex (sixVertexFourByTwoOrientedNorthSeed, true)) = true := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoParity_north

/--
[sixVertexFourByTwoPhysicalReturn_seed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedPhysicalKeyCounterexample.lean)
-/
@[path]
private lemma sixVertexFourByTwoPhysicalReturn_seed_eq :
-- imply
  sixVertexDegreeTwoSynchronizedComponentPhysicalReturnState sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice sixVertexFourByTwo_locallyDegreeTwo sixVertexFourByTwoSynchronizedSeedComponent false (sixVertexFourByTwoOrientedSeed, false) = (sixVertexFourByTwoOrientedNorthSeed, false) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoPhysicalReturn_seed

/--
[sixVertexFourByTwoActiveColor_true_seed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedPhysicalKeyCounterexample.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveColor_true_seed_eq :
-- imply
  sixVertexDegreeTwoAlignedActiveColor sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice sixVertexFourByTwo_locallyDegreeTwo true (sixVertexFourByTwoOrientedSeed, false) = false := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveColor_true_seed

/--
[sixVertexFourByTwoActiveColor_false_north](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedPhysicalKeyCounterexample.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveColor_false_north_eq :
-- imply
  sixVertexDegreeTwoAlignedActiveColor sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice sixVertexFourByTwo_locallyDegreeTwo false (sixVertexFourByTwoOrientedNorthSeed, false) = true := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveColor_false_north

/--
[sixVertexFourByTwo_not_activeReturnColorInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedPhysicalKeyCounterexample.lean)
-/
@[path]
private lemma sixVertexFourByTwo_not_activeReturnColorInvariant_eq :
-- imply
  ¬ SixVertexDegreeTwoSynchronizedComponentActiveReturnColorInvariant sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice sixVertexFourByTwo_locallyDegreeTwo sixVertexFourByTwoSynchronizedSeedComponent := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwo_not_activeReturnColorInvariant

/--
[sixVertexFourByTwo_not_synchronizedActiveStepColorInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedPhysicalKeyCounterexample.lean)
-/
@[path]
private lemma sixVertexFourByTwo_not_synchronizedActiveStepColorInvariant_eq :
-- imply
  ¬ SixVertexFourByTwoSynchronizedActiveStepColorInvariant := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwo_not_synchronizedActiveStepColorInvariant


-- created on 2026-10-23

import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePartialEdgeCopySwitching.Part6
open SimpleGraph Finset BigOperators StatMech StatMech.Sharpness StatMech.Sharpness.BackboneLabeledSwitching


/--
[shb_vacuumPartialSelector_admissible_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialEdgeCopySwitching.lean)
-/
@[path]
private lemma shb_vacuumPartialSelector_admissible_iff_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
-- given
  (m : d.graph.edgeFinset -> Nat) :
-- imply
  shb_vacuumPartialSelector.Admissible d m <-> sources d.graph (ofEdgeFun d.graph m) = ∅ := by
-- proof
  apply StatMech.Sharpness.shb_vacuumPartialSelector_admissible_iff d m

/--
[shb_oneStepCandidate_of_chosen_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialEdgeCopySwitching.lean)
-/
@[path]
private lemma shb_oneStepCandidate_of_chosen_eq_some_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
-- given
  (m : d.graph.edgeFinset -> Nat)
  (h : shb_oneStepChosenSegment d m = some s) :
-- imply
  shb_oneStepCandidate d m s := by
-- proof
  apply StatMech.Sharpness.shb_oneStepCandidate_of_chosen_eq_some d m s h

/--
[shb_oneStepPartialSelector_admissible_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialEdgeCopySwitching.lean)
-/
@[path]
private lemma shb_oneStepPartialSelector_admissible_iff_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
-- given
  (m : d.graph.edgeFinset -> Nat) :
-- imply
  shb_oneStepPartialSelector.Admissible d m <-> sources d.graph (ofEdgeFun d.graph m) = ∅ ∨ ∃ s, shb_oneStepCandidate d m s := by
-- proof
  apply StatMech.Sharpness.shb_oneStepPartialSelector_admissible_iff d m

/--
[toggleEquiv_weight_preserving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialEdgeCopySwitching.lean)
-/
@[path]
private lemma toggleEquiv_weight_preserving_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {A C : Finset V}
  {P : Finset (FluxEdgeCopy.Copy G m)}
  {S : Fiber G m A Q}
-- given
  (J : Sym2 V -> Real)
  (m : G.edgeFinset -> Nat)
  (hPsrc : RandomCurrent.sources (endsM G m) P = C)
  (Q R : Finset (FluxEdgeCopy.Copy G m) -> Prop)
  (htransport : ∀ S, Q S <-> R (S ∆ P)) :
-- imply
  labeledWeight G beta J m S.1 = labeledWeight G beta J m ((toggleEquiv G m A C P hPsrc Q R htransport S).1) := by
-- proof
  apply StatMech.Sharpness.BackboneLabeledSwitching.toggleEquiv_weight_preserving G beta J m A C P hPsrc Q R htransport S

/--
[sum_labeledWeight_toggle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialEdgeCopySwitching.lean)
-/
@[path]
private lemma sum_labeledWeight_toggle_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {A C : Finset V}
  {P : Finset (FluxEdgeCopy.Copy G m)}
  [DecidablePred Q]
  [DecidablePred R]
-- given
  (J : Sym2 V -> Real)
  (m : G.edgeFinset -> Nat)
  (hPsrc : RandomCurrent.sources (endsM G m) P = C)
  (Q R : Finset (FluxEdgeCopy.Copy G m) -> Prop)
  (htransport : ∀ S, Q S <-> R (S ∆ P)) :
-- imply
  (∑ S : Fiber G m A Q, labeledWeight G beta J m S.1) = ∑ T : Fiber G m (A ∆ C) R, labeledWeight G beta J m T.1 := by
-- proof
  apply StatMech.Sharpness.BackboneLabeledSwitching.sum_labeledWeight_toggle G beta J m A C P hPsrc Q R htransport

/--
[rawPairFiberMass_tsum_eq_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialEdgeCopySwitching.lean)
-/
@[path]
private lemma rawPairFiberMass_tsum_eq_mul_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  [DecidablePred Q]
  [DecidablePred R]
-- given
  (J : Sym2 V -> Real)
  (Q R : (G.edgeFinset -> Nat) -> Prop) :
-- imply
  (∑' p : G.edgeFinset -> Nat, if Q p then weight G beta J (ofEdgeFun G p) else 0) * (∑' q : G.edgeFinset -> Nat, if R q then weight G beta J (ofEdgeFun G q) else 0) = ∑' m : G.edgeFinset -> Nat, rawPairFiberMass G beta J m Q R := by
-- proof
  apply StatMech.Sharpness.BackboneLabeledSwitching.rawPairFiberMass_tsum_eq_mul G beta J Q R

/--
[rawFiberMass_eq_rawPairFiberMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialEdgeCopySwitching.lean)
-/
@[path]
private lemma rawFiberMass_eq_rawPairFiberMass_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {A : Finset V}
  [DecidablePred Q]
-- given
  (J : Sym2 V -> Real)
  (m : G.edgeFinset -> Nat)
  (Q : (G.edgeFinset -> Nat) -> Prop) :
-- imply
  rawFiberMass G beta J m A Q = rawPairFiberMass G beta J m (fun p => sources G (ofEdgeFun G p) = A ∧ Q p) (fun _ => True) := by
-- proof
  apply StatMech.Sharpness.BackboneLabeledSwitching.rawFiberMass_eq_rawPairFiberMass G beta J m A Q

/--
[tsum_rawFiberMass_eq_mul_unrestricted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialEdgeCopySwitching.lean)
-/
@[path]
private lemma tsum_rawFiberMass_eq_mul_unrestricted_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {A : Finset V}
  [DecidablePred Q]
-- given
  (J : Sym2 V -> Real)
  (Q : (G.edgeFinset -> Nat) -> Prop) :
-- imply
  (∑' m : G.edgeFinset -> Nat, rawFiberMass G beta J m A Q) = (∑' p : G.edgeFinset -> Nat, if sources G (ofEdgeFun G p) = A ∧ Q p then weight G beta J (ofEdgeFun G p) else 0) * (∑' q : G.edgeFinset -> Nat, weight G beta J (ofEdgeFun G q)) := by
-- proof
  apply StatMech.Sharpness.BackboneLabeledSwitching.tsum_rawFiberMass_eq_mul_unrestricted G beta J A Q

/--
[rawPredicateMass_eq_labeled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialEdgeCopySwitching.lean)
-/
@[path]
private lemma rawPredicateMass_eq_labeled_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  [DecidablePred Q]
-- given
  (J : Sym2 V -> Real)
  (m : G.edgeFinset -> Nat)
  (Q : (G.edgeFinset -> Nat) -> Prop) :
-- imply
  (∑ K : {p : G.edgeFinset -> Nat // p <= m}, if Q K.1 then rawSplitWeight G beta J m K else 0) = ∑ S : Finset (FluxEdgeCopy.Copy G m), if Q (profileFlux G m S) then labeledWeight G beta J m S else 0 := by
-- proof
  apply StatMech.Sharpness.BackboneLabeledSwitching.rawPredicateMass_eq_labeled G beta J m Q

/--
[rawFiberMass_eq_labeledFiberMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialEdgeCopySwitching.lean)
-/
@[path]
private lemma rawFiberMass_eq_labeledFiberMass_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {A : Finset V}
  [DecidablePred Q]
-- given
  (J : Sym2 V -> Real)
  (m : G.edgeFinset -> Nat)
  (Q : (G.edgeFinset -> Nat) -> Prop) :
-- imply
  rawFiberMass G beta J m A Q = labeledFiberMass G beta J m A Q := by
-- proof
  apply StatMech.Sharpness.BackboneLabeledSwitching.rawFiberMass_eq_labeledFiberMass G beta J m A Q

/--
[rawFiberMass_eq_of_labeledToggle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialEdgeCopySwitching.lean)
-/
@[path]
private lemma rawFiberMass_eq_of_labeledToggle_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {A C : Finset V}
  {P : Finset (FluxEdgeCopy.Copy G m)}
  [DecidablePred Q]
  [DecidablePred R]
-- given
  (J : Sym2 V -> Real)
  (m : G.edgeFinset -> Nat)
  (hPsrc : RandomCurrent.sources (endsM G m) P = C)
  (Q R : (G.edgeFinset -> Nat) -> Prop)
  (htransport : ∀ S, Q (profileFlux G m S) <-> R (profileFlux G m (S ∆ P))) :
-- imply
  rawFiberMass G beta J m A Q = rawFiberMass G beta J m (A ∆ C) R := by
-- proof
  apply StatMech.Sharpness.BackboneLabeledSwitching.rawFiberMass_eq_of_labeledToggle G beta J m A C P hPsrc Q R htransport


-- created on 2026-10-23

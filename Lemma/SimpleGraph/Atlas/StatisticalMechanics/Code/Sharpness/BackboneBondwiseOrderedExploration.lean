import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.BackboneBondwiseOrderedExploration
open Finset StatMech StatMech.Sharpness StatMech.Sharpness.shb_bondwiseOrderedTests StatMech.Sharpness.shb_DynamicEdgeExploration StatMech.Sharpness.BackboneDeterminedCutSwitching


/--
[test_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneBondwiseOrderedExploration.lean)
-/
@[path]
private lemma test_apply_eq
  [DecidableEq B]
  {order : List B}
  {b : B}
-- given
  (hnodup : order.Nodup)
  (omega : B -> Bool) :
-- imply
  (shb_bondwiseOrderedTests order hnodup).test omega b = omega b := by
-- proof
  apply StatMech.Sharpness.shb_bondwiseOrderedTests.test_apply order hnodup omega b

/--
[exposure_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneBondwiseOrderedExploration.lean)
-/
@[path]
private lemma exposure_apply_eq
  [DecidableEq B]
  {order : List B}
  {b : B}
-- given
  (hnodup : order.Nodup) :
-- imply
  (shb_bondwiseOrderedTests order hnodup).exposure b = {b} := by
-- proof
  apply StatMech.Sharpness.shb_bondwiseOrderedTests.exposure_apply order hnodup b

/--
[mem_determinedCut_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneBondwiseOrderedExploration.lean)
-/
@[path]
private lemma mem_determinedCut_iff_eq
  [DecidableEq B]
  {order : List B}
  {accepted b : B}
-- given
  (hnodup : order.Nodup) :
-- imply
  b ∈ (shb_bondwiseOrderedTests order hnodup).determinedCut accepted <-> b ∈ (shb_bondwiseOrderedTests order hnodup).testedThrough accepted := by
-- proof
  apply StatMech.Sharpness.shb_bondwiseOrderedTests.mem_determinedCut_iff order hnodup accepted b

/--
[rejected_mem_determinedCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneBondwiseOrderedExploration.lean)
-/
@[path]
private lemma rejected_mem_determinedCut_eq
  [DecidableEq B]
  {order : List B}
  {accepted rejected : B}
-- given
  (hnodup : order.Nodup)
  (hrejected : rejected ∈ order.takeWhile (fun b => b != accepted)) :
-- imply
  rejected ∈ (shb_bondwiseOrderedTests order hnodup).determinedCut accepted := by
-- proof
  apply StatMech.Sharpness.shb_bondwiseOrderedTests.rejected_mem_determinedCut order hnodup accepted rejected hrejected

/--
[accepted_mem_determinedCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneBondwiseOrderedExploration.lean)
-/
@[path]
private lemma accepted_mem_determinedCut_eq
  [DecidableEq B]
  {order : List B}
  {accepted : B}
-- given
  (hnodup : order.Nodup) :
-- imply
  accepted ∈ (shb_bondwiseOrderedTests order hnodup).determinedCut accepted := by
-- proof
  apply StatMech.Sharpness.shb_bondwiseOrderedTests.accepted_mem_determinedCut order hnodup accepted

/--
[bondwiseOrdered_tests_order](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneBondwiseOrderedExploration.lean)
-/
@[path]
private lemma bondwiseOrdered_tests_order_eq
  [DecidableEq B]
  {X : shb_DynamicEdgeExploration D B}
  {d : D} :
-- imply
  ((X.bondwiseOrdered).tests d).order = X.edgeOrder d := by
-- proof
  apply StatMech.Sharpness.shb_DynamicEdgeExploration.bondwiseOrdered_tests_order X d

/--
[bondwiseOrdered_advance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneBondwiseOrderedExploration.lean)
-/
@[path]
private lemma bondwiseOrdered_advance_eq
  [DecidableEq B]
  {X : shb_DynamicEdgeExploration D B}
  {d : D}
  {b : B} :
-- imply
  X.bondwiseOrdered.advance d b = X.advance d b := by
-- proof
  apply StatMech.Sharpness.shb_DynamicEdgeExploration.bondwiseOrdered_advance X d b

/--
[bondwiseOrdered_selects_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneBondwiseOrderedExploration.lean)
-/
@[path]
private lemma bondwiseOrdered_selects_iff_eq
  [DecidableEq B]
  {X : shb_DynamicEdgeExploration D B}
  {d : D}
  {word : List B}
-- given
  (omega : B -> Bool) :
-- imply
  X.bondwiseOrdered.Selects omega d word <-> X.Selects (fun _ b => omega b) d word := by
-- proof
  apply StatMech.Sharpness.shb_DynamicEdgeExploration.bondwiseOrdered_selects_iff X omega d word

/--
[mem_bondwiseOrdered_determinedCut_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneBondwiseOrderedExploration.lean)
-/
@[path]
private lemma mem_bondwiseOrdered_determinedCut_iff_eq
  [DecidableEq B]
  {X : shb_DynamicEdgeExploration D B}
  {d : D}
  {accepted b : B} :
-- imply
  b ∈ ((X.bondwiseOrdered).tests d).determinedCut accepted <-> b ∈ X.determinedAt d accepted := by
-- proof
  apply StatMech.Sharpness.shb_DynamicEdgeExploration.mem_bondwiseOrdered_determinedCut_iff X d accepted b

/--
[mem_bondwiseOrdered_traceCut_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneBondwiseOrderedExploration.lean)
-/
@[path]
private lemma mem_bondwiseOrdered_traceCut_iff_eq
  [DecidableEq B]
  {X : shb_DynamicEdgeExploration D B}
  {d : D}
  {word : List B}
  {b : B} :
-- imply
  b ∈ X.bondwiseOrdered.traceCut d word <-> b ∈ X.determinedTrace d word := by
-- proof
  apply StatMech.Sharpness.shb_DynamicEdgeExploration.mem_bondwiseOrdered_traceCut_iff X d word b

/--
[selects_iff_of_agreeOn_determinedTrace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneBondwiseOrderedExploration.lean)
-/
@[path]
private lemma selects_iff_of_agreeOn_determinedTrace_eq
  [DecidableEq B]
  {X : shb_DynamicEdgeExploration D B}
  {d : D}
  {word : List B}
-- given
  (omega eta : B -> Bool)
  (hagree : ∀ b ∈ X.determinedTrace d word, omega b = eta b) :
-- imply
  X.Selects (fun _ b => omega b) d word <-> X.Selects (fun _ b => eta b) d word := by
-- proof
  apply StatMech.Sharpness.shb_DynamicEdgeExploration.selects_iff_of_agreeOn_determinedTrace X omega eta d word hagree

/--
[profileFlux_eq_of_outsideCopies_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneBondwiseOrderedExploration.lean)
-/
@[path]
private lemma profileFlux_eq_of_outsideCopies_eq_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {cut : Set (Sym2 V)}
  {S T : Finset (FluxEdgeCopy.Copy G m)}
  {e : G.edgeFinset}
-- given
  (m : G.edgeFinset -> Nat)
  (hout : outsideCopies G m cut S = outsideCopies G m cut T)
  (he : e.1 ∉ cut) :
-- imply
  profileFlux G m S e = profileFlux G m T e := by
-- proof
  apply StatMech.Sharpness.BackboneDeterminedCutSwitching.profileFlux_eq_of_outsideCopies_eq G m cut S T hout e he

/--
[fluxBitConfig_eq_on_freshSuffix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneBondwiseOrderedExploration.lean)
-/
@[path]
private lemma fluxBitConfig_eq_on_freshSuffix_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {X : shb_DynamicEdgeExploration D (Sym2 V)}
  {d : D}
  {accepted : Sym2 V}
  {suffix : List (Sym2 V)}
  {S T : Finset (FluxEdgeCopy.Copy G m)}
-- given
  (hfresh : SuffixFresh X d accepted suffix)
  (bit : Nat -> Bool)
  (m : G.edgeFinset -> Nat)
  (hout : outsideCopies G m ((X.bondwiseOrdered.tests d).determinedCut accepted) S = outsideCopies G m ((X.bondwiseOrdered.tests d).determinedCut accepted) T) :
-- imply
  ∀ e ∈ X.determinedTrace (X.advance d accepted) suffix, fluxBitConfig G bit (profileFlux G m S) e = fluxBitConfig G bit (profileFlux G m T) e := by
-- proof
  apply StatMech.Sharpness.BackboneDeterminedCutSwitching.fluxBitConfig_eq_on_freshSuffix G X d accepted suffix hfresh bit m S T hout

/--
[bondwiseSuffixEvent_fluxEventOutsideCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneBondwiseOrderedExploration.lean)
-/
@[path]
private lemma bondwiseSuffixEvent_fluxEventOutsideCut_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {X : shb_DynamicEdgeExploration D (Sym2 V)}
  {d : D}
  {accepted : Sym2 V}
  {suffix : List (Sym2 V)}
-- given
  (hfresh : SuffixFresh X d accepted suffix)
  (bit : Nat -> Bool)
  (m : G.edgeFinset -> Nat) :
-- imply
  FluxEventOutsideCut G m ((X.bondwiseOrdered.tests d).determinedCut accepted) (BondwiseSuffixEvent G X (X.advance d accepted) suffix bit) := by
-- proof
  apply StatMech.Sharpness.BackboneDeterminedCutSwitching.bondwiseSuffixEvent_fluxEventOutsideCut G X d accepted suffix hfresh bit m

/--
[rawFiberMass_eq_of_bondwiseDeterminedToggle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneBondwiseOrderedExploration.lean)
-/
@[path]
private lemma rawFiberMass_eq_of_bondwiseDeterminedToggle_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {X : shb_DynamicEdgeExploration D (Sym2 V)}
  {d : D}
  {accepted : Sym2 V}
  {beta : Real}
  {A C : Finset V}
  {P : Finset (FluxEdgeCopy.Copy G m)}
  [DecidablePred Q]
-- given
  (J : Sym2 V -> Real)
  (m : G.edgeFinset -> Nat)
  (hPsrc : RandomCurrent.sources (endsM G m) P = C)
  (hPcut : SupportedInCut G m ((X.bondwiseOrdered.tests d).determinedCut accepted) P)
  (Q : (G.edgeFinset -> Nat) -> Prop)
  (hQ : FluxEventOutsideCut G m ((X.bondwiseOrdered.tests d).determinedCut accepted) Q) :
-- imply
  rawFiberMass G beta J m A Q = rawFiberMass G beta J m (A ∆ C) Q := by
-- proof
  apply StatMech.Sharpness.BackboneDeterminedCutSwitching.rawFiberMass_eq_of_bondwiseDeterminedToggle G X d accepted beta J m A C P hPsrc hPcut Q hQ

/--
[rawFiberMass_eq_of_bondwiseSuffixToggle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneBondwiseOrderedExploration.lean)
-/
@[path]
private lemma rawFiberMass_eq_of_bondwiseSuffixToggle_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {X : shb_DynamicEdgeExploration D (Sym2 V)}
  {d : D}
  {accepted : Sym2 V}
  {suffix : List (Sym2 V)}
  {beta : Real}
  {A C : Finset V}
  {P : Finset (FluxEdgeCopy.Copy G m)}
-- given
  (hfresh : SuffixFresh X d accepted suffix)
  (bit : Nat -> Bool)
  (J : Sym2 V -> Real)
  (m : G.edgeFinset -> Nat)
  (hPsrc : RandomCurrent.sources (endsM G m) P = C)
  (hPcut : SupportedInCut G m ((X.bondwiseOrdered.tests d).determinedCut accepted) P) :
-- imply
  rawFiberMass G beta J m A (BondwiseSuffixEvent G X (X.advance d accepted) suffix bit) = rawFiberMass G beta J m (A ∆ C) (BondwiseSuffixEvent G X (X.advance d accepted) suffix bit) := by
-- proof
  apply StatMech.Sharpness.BackboneDeterminedCutSwitching.rawFiberMass_eq_of_bondwiseSuffixToggle G X d accepted suffix hfresh bit beta J m A C P hPsrc hPcut

/--
[BondwiseP2Reindex.path_source_eq_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneBondwiseOrderedExploration.lean)
-/
@[path]
private lemma path_source_eq_empty_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {X : shb_DynamicEdgeExploration D (Sym2 V)}
  {x : D}
  {accepted : Sym2 V}
  {suffix : List (Sym2 V)}
  {A C : Finset V}
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
  {ss : List (shb_ExplorationSegment V)}
  {R : BondwiseP2Reindex X x accepted suffix bit A C S beta J d s ss}
-- given
  (bit : Nat -> Bool)
  (S : shb_CurrentDynamicSelector (V := V))
  (J : Sym2 V -> Real) :
-- imply
  C = ∅ := by
-- proof
  apply StatMech.Sharpness.BackboneDeterminedCutSwitching.BondwiseP2Reindex.path_source_eq_empty G X x accepted suffix bit A C S beta J d s ss R

/--
[bondwiseP2Reindex_isEmpty_of_path_source_ne_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneBondwiseOrderedExploration.lean)
-/
@[path]
private lemma bondwiseP2Reindex_isEmpty_of_path_source_ne_empty_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {X : shb_DynamicEdgeExploration D (Sym2 V)}
  {x : D}
  {accepted : Sym2 V}
  {suffix : List (Sym2 V)}
  {A C : Finset V}
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
  {ss : List (shb_ExplorationSegment V)}
-- given
  (bit : Nat -> Bool)
  (S : shb_CurrentDynamicSelector (V := V))
  (J : Sym2 V -> Real)
  (hC : C ≠ ∅) :
-- imply
  IsEmpty (BondwiseP2Reindex X x accepted suffix bit A C S beta J d s ss) := by
-- proof
  apply StatMech.Sharpness.BackboneDeterminedCutSwitching.bondwiseP2Reindex_isEmpty_of_path_source_ne_empty G X x accepted suffix bit A C S beta J d s ss hC

/--
[actualMass_active_of_bondwiseSuffixToggle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneBondwiseOrderedExploration.lean)
-/
@[path]
private lemma actualMass_active_of_bondwiseSuffixToggle_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {X : shb_DynamicEdgeExploration D (Sym2 V)}
  {x : D}
  {accepted : Sym2 V}
  {suffix : List (Sym2 V)}
  {A C : Finset V}
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
  {ss : List (shb_ExplorationSegment V)}
  {R : BondwiseP2Reindex X x accepted suffix bit A C S beta J d s ss}
-- given
  (hfresh : SuffixFresh X x accepted suffix)
  (bit : Nat -> Bool)
  (S : shb_CurrentDynamicSelector (V := V))
  (J : Sym2 V -> Real) :
-- imply
  S.actualMass beta J d (s :: ss) * currentSum (shb_BackboneExplorationDomain.advance d s).graph beta J ∅ = shb_segmentNum beta J d s * S.actualMass beta J (shb_BackboneExplorationDomain.advance d s) ss := by
-- proof
  apply StatMech.Sharpness.BackboneDeterminedCutSwitching.actualMass_active_of_bondwiseSuffixToggle G X x accepted suffix hfresh bit A C S beta J d s ss R


-- created on 2026-10-23

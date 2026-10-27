import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneOrderedDeterminedCut.Part4
open Finset BigOperators StatMech StatMech.Sharpness StatMech.Sharpness.shb_OrderedLocalTests StatMech.Sharpness.shb_OrderedLocalExploration StatMech.Sharpness.BackboneDeterminedCutSwitching


/--
[accepted_mem_testedThrough](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneOrderedDeterminedCut.lean)
-/
@[path]
private lemma accepted_mem_testedThrough_eq
  [DecidableEq E]
  {T : shb_OrderedLocalTests E B}
  {accepted : E} :
-- imply
  accepted ∈ T.testedThrough accepted := by
-- proof
  apply StatMech.Sharpness.shb_OrderedLocalTests.accepted_mem_testedThrough T accepted

/--
[exposure_subset_determinedCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneOrderedDeterminedCut.lean)
-/
@[path]
private lemma exposure_subset_determinedCut_eq
  [DecidableEq E]
  {T : shb_OrderedLocalTests E B}
  {accepted e : E}
-- given
  (he : e ∈ T.testedThrough accepted) :
-- imply
  T.exposure e ⊆ T.determinedCut accepted := by
-- proof
  apply StatMech.Sharpness.shb_OrderedLocalTests.exposure_subset_determinedCut T accepted e he

/--
[test_eq_of_mem_testedThrough](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneOrderedDeterminedCut.lean)
-/
@[path]
private lemma test_eq_of_mem_testedThrough_eq
  [DecidableEq E]
  {T : shb_OrderedLocalTests E B}
  {accepted e : E}
-- given
  (omega eta : B -> Bool)
  (hagree : ∀ b ∈ T.determinedCut accepted, omega b = eta b)
  (he : e ∈ T.testedThrough accepted) :
-- imply
  T.test omega e = T.test eta e := by
-- proof
  apply StatMech.Sharpness.shb_OrderedLocalTests.test_eq_of_mem_testedThrough T omega eta accepted e hagree he

/--
[find](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneOrderedDeterminedCut.lean)
-/
@[path]
private lemma find_eq
  [DecidableEq E]
  {order : List E}
  {accepted : E}
-- given
  (test₁ test₂ : E -> Bool)
  (hnodup : order.Nodup)
  (hfind : order.find? test₁ = some accepted)
  (hagree : ∀ e ∈ order.takeWhile (fun t => t != accepted) ++ [accepted], test₁ e = test₂ e) :
-- imply
  order.find? test₂ = some accepted := by
-- proof
  apply StatMech.Sharpness.shb_OrderedLocalTests.find test₁ test₂ order accepted hnodup hfind hagree

/--
[firstAccepted_eq_of_agreeOn_determinedCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneOrderedDeterminedCut.lean)
-/
@[path]
private lemma firstAccepted_eq_of_agreeOn_determinedCut_eq
  [DecidableEq E]
  {T : shb_OrderedLocalTests E B}
  {accepted : E}
-- given
  (omega eta : B -> Bool)
  (hfind : T.order.find? (T.test omega) = some accepted)
  (hagree : ∀ b ∈ T.determinedCut accepted, omega b = eta b) :
-- imply
  T.order.find? (T.test eta) = some accepted := by
-- proof
  apply StatMech.Sharpness.shb_OrderedLocalTests.firstAccepted_eq_of_agreeOn_determinedCut T omega eta accepted hfind hagree

/--
[firstAccepted_iff_of_agreeOn_determinedCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneOrderedDeterminedCut.lean)
-/
@[path]
private lemma firstAccepted_iff_of_agreeOn_determinedCut_eq
  [DecidableEq E]
  {T : shb_OrderedLocalTests E B}
  {accepted : E}
-- given
  (omega eta : B -> Bool)
  (hagree : ∀ b ∈ T.determinedCut accepted, omega b = eta b) :
-- imply
  T.order.find? (T.test omega) = some accepted <-> T.order.find? (T.test eta) = some accepted := by
-- proof
  apply StatMech.Sharpness.shb_OrderedLocalTests.firstAccepted_iff_of_agreeOn_determinedCut T omega eta accepted hagree

/--
[selects_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneOrderedDeterminedCut.lean)
-/
@[path]
private lemma selects_nil_eq
  [DecidableEq E]
  {X : shb_OrderedLocalExploration D E B}
  {d : D}
-- given
  (omega : B -> Bool) :
-- imply
  X.Selects omega d [] := by
-- proof
  apply StatMech.Sharpness.shb_OrderedLocalExploration.selects_nil X omega d

/--
[selects_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneOrderedDeterminedCut.lean)
-/
@[path]
private lemma selects_cons_eq
  [DecidableEq E]
  {X : shb_OrderedLocalExploration D E B}
  {d : D}
  {e : E}
  {es : List E}
-- given
  (omega : B -> Bool) :
-- imply
  X.Selects omega d (e :: es) <-> (X.tests d).order.find? ((X.tests d).test omega) = some e ∧ X.Selects omega (X.advance d e) es := by
-- proof
  apply StatMech.Sharpness.shb_OrderedLocalExploration.selects_cons X omega d e es

/--
[traceCut_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneOrderedDeterminedCut.lean)
-/
@[path]
private lemma traceCut_nil_eq
  [DecidableEq E]
  {X : shb_OrderedLocalExploration D E B}
  {d : D} :
-- imply
  X.traceCut d [] = ∅ := by
-- proof
  apply StatMech.Sharpness.shb_OrderedLocalExploration.traceCut_nil X d

/--
[traceCut_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneOrderedDeterminedCut.lean)
-/
@[path]
private lemma traceCut_cons_eq
  [DecidableEq E]
  {X : shb_OrderedLocalExploration D E B}
  {d : D}
  {e : E}
  {es : List E} :
-- imply
  X.traceCut d (e :: es) = (X.tests d).determinedCut e ∪ X.traceCut (X.advance d e) es := by
-- proof
  apply StatMech.Sharpness.shb_OrderedLocalExploration.traceCut_cons X d e es

/--
[selects_iff_of_agreeOn_traceCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneOrderedDeterminedCut.lean)
-/
@[path]
private lemma selects_iff_of_agreeOn_traceCut_eq
  [DecidableEq E]
  {X : shb_OrderedLocalExploration D E B}
  {d : D}
  {word : List E}
-- given
  (omega eta : B -> Bool)
  (hagree : ∀ b ∈ X.traceCut d word, omega b = eta b) :
-- imply
  X.Selects omega d word <-> X.Selects eta d word := by
-- proof
  apply StatMech.Sharpness.shb_OrderedLocalExploration.selects_iff_of_agreeOn_traceCut X omega eta d word hagree

/--
[outsideCopies_symmDiff_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneOrderedDeterminedCut.lean)
-/
@[path]
private lemma outsideCopies_symmDiff_eq_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {cut : Set (Sym2 V)}
  {S P : Finset (FluxEdgeCopy.Copy G m)}
-- given
  (m : G.edgeFinset -> Nat)
  (hP : SupportedInCut G m cut P) :
-- imply
  outsideCopies G m cut (S ∆ P) = outsideCopies G m cut S := by
-- proof
  apply StatMech.Sharpness.BackboneDeterminedCutSwitching.outsideCopies_symmDiff_eq G m cut S P hP

/--
[fluxEvent_toggle_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneOrderedDeterminedCut.lean)
-/
@[path]
private lemma fluxEvent_toggle_iff_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {cut : Set (Sym2 V)}
  {S P : Finset (FluxEdgeCopy.Copy G m)}
-- given
  (m : G.edgeFinset -> Nat)
  (Q : (G.edgeFinset -> Nat) -> Prop)
  (hQ : FluxEventOutsideCut G m cut Q)
  (hP : SupportedInCut G m cut P) :
-- imply
  Q (profileFlux G m S) <-> Q (profileFlux G m (S ∆ P)) := by
-- proof
  apply StatMech.Sharpness.BackboneDeterminedCutSwitching.fluxEvent_toggle_iff G m cut Q hQ S P hP

/--
[rawFiberMass_eq_of_determinedCutToggle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneOrderedDeterminedCut.lean)
-/
@[path]
private lemma rawFiberMass_eq_of_determinedCutToggle_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {A C : Finset V}
  {cut : Set (Sym2 V)}
  {P : Finset (FluxEdgeCopy.Copy G m)}
  [DecidablePred Q]
-- given
  (J : Sym2 V -> Real)
  (m : G.edgeFinset -> Nat)
  (hPsrc : RandomCurrent.sources (endsM G m) P = C)
  (hPcut : SupportedInCut G m cut P)
  (Q : (G.edgeFinset -> Nat) -> Prop)
  (hQ : FluxEventOutsideCut G m cut Q) :
-- imply
  rawFiberMass G beta J m A Q = rawFiberMass G beta J m (A ∆ C) Q := by
-- proof
  apply StatMech.Sharpness.BackboneDeterminedCutSwitching.rawFiberMass_eq_of_determinedCutToggle G beta J m A C cut P hPsrc hPcut Q hQ

/--
[rawFiberMass_eq_of_orderedDeterminedToggle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneOrderedDeterminedCut.lean)
-/
@[path]
private lemma rawFiberMass_eq_of_orderedDeterminedToggle_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq E]
  {T : shb_OrderedLocalTests E (Sym2 V)}
  {accepted : E}
  {beta : Real}
  {A C : Finset V}
  {P : Finset (FluxEdgeCopy.Copy G m)}
  [DecidablePred Q]
-- given
  (J : Sym2 V -> Real)
  (m : G.edgeFinset -> Nat)
  (hPsrc : RandomCurrent.sources (endsM G m) P = C)
  (hPcut : SupportedInCut G m (T.determinedCut accepted) P)
  (Q : (G.edgeFinset -> Nat) -> Prop)
  (hQ : FluxEventOutsideCut G m (T.determinedCut accepted) Q) :
-- imply
  rawFiberMass G beta J m A Q = rawFiberMass G beta J m (A ∆ C) Q := by
-- proof
  apply StatMech.Sharpness.BackboneDeterminedCutSwitching.rawFiberMass_eq_of_orderedDeterminedToggle G T accepted beta J m A C P hPsrc hPcut Q hQ


-- created on 2026-10-23

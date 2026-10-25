import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePartialP2Reindex.Part3
open SimpleGraph Finset BigOperators StatMech StatMech.Sharpness StatMech.Sharpness.BackboneLabeledSwitching StatMech.Sharpness.BackboneDeterminedCutSwitching StatMech.Sharpness.shb_PartialCurrentDynamicSelector StatMech.Sharpness.BackbonePartialP2Reindex


/--
[rawSourcePairFiberMass_eq_labeled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialP2Reindex.lean)
-/
@[path]
private lemma rawSourcePairFiberMass_eq_labeled_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {A : Finset V}
  [DecidablePred Q]
  [DecidablePred R]
-- given
  (J : Sym2 V -> Real)
  (m : G.edgeFinset -> Nat)
  (Q R : (G.edgeFinset -> Nat) -> Prop) :
-- imply
  rawSourcePairFiberMass G beta J m A Q R = labeledSourcePairFiberMass G beta J m A Q R := by
-- proof
  apply StatMech.Sharpness.BackboneLabeledSwitching.rawSourcePairFiberMass_eq_labeled G beta J m A Q R

/--
[rawSourcePairFiberMass_eq_of_labeledToggle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialP2Reindex.lean)
-/
@[path]
private lemma rawSourcePairFiberMass_eq_of_labeledToggle_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {A C : Finset V}
  {P : Finset (FluxEdgeCopy.Copy G m)}
  [DecidablePred Q₁]
  [DecidablePred R₁]
  [DecidablePred Q₂]
  [DecidablePred R₂]
-- given
  (J : Sym2 V -> Real)
  (m : G.edgeFinset -> Nat)
  (hPsrc : RandomCurrent.sources (endsM G m) P = C)
  (Q₁ R₁ Q₂ R₂ : (G.edgeFinset -> Nat) -> Prop)
  (htransport : ∀ S, (Q₁ (profileFlux G m S) ∧ R₁ (profileFlux G m (univ \ S))) <-> (Q₂ (profileFlux G m (S ∆ P)) ∧ R₂ (profileFlux G m (univ \ (S ∆ P))))) :
-- imply
  rawSourcePairFiberMass G beta J m A Q₁ R₁ = rawSourcePairFiberMass G beta J m (A ∆ C) Q₂ R₂ := by
-- proof
  apply StatMech.Sharpness.BackboneLabeledSwitching.rawSourcePairFiberMass_eq_of_labeledToggle G beta J m A C P hPsrc Q₁ R₁ Q₂ R₂ htransport

/--
[compl_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialP2Reindex.lean)
-/
@[path]
private lemma compl_symmDiff_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S P : Finset (FluxEdgeCopy.Copy G m)}
-- given
  (m : G.edgeFinset -> Nat) :
-- imply
  univ \ (S ∆ P) = (univ \ S) ∆ P := by
-- proof
  apply StatMech.Sharpness.BackboneDeterminedCutSwitching.compl_symmDiff G m S P

/--
[pairTransport_of_fluxEventsOutsideCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialP2Reindex.lean)
-/
@[path]
private lemma pairTransport_of_fluxEventsOutsideCut_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {cut : Set (Sym2 V)}
  {P : Finset (FluxEdgeCopy.Copy G m)}
  {S : Finset (FluxEdgeCopy.Copy G m)}
-- given
  (m : G.edgeFinset -> Nat)
  (Q R : (G.edgeFinset -> Nat) -> Prop)
  (hQ : FluxEventOutsideCut G m cut Q)
  (hR : FluxEventOutsideCut G m cut R)
  (hP : SupportedInCut G m cut P) :
-- imply
  (Q (profileFlux G m S) ∧ R (profileFlux G m (univ \ S))) <-> (Q (profileFlux G m (S ∆ P)) ∧ R (profileFlux G m (univ \ (S ∆ P)))) := by
-- proof
  apply StatMech.Sharpness.BackboneDeterminedCutSwitching.pairTransport_of_fluxEventsOutsideCut G m cut Q R hQ hR P hP S

/--
[rawSourcePairFiberMass_eq_of_determinedCutToggle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialP2Reindex.lean)
-/
@[path]
private lemma rawSourcePairFiberMass_eq_of_determinedCutToggle_eq
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
  [DecidablePred R]
-- given
  (J : Sym2 V -> Real)
  (m : G.edgeFinset -> Nat)
  (hPsrc : RandomCurrent.sources (endsM G m) P = C)
  (hPcut : SupportedInCut G m cut P)
  (Q R : (G.edgeFinset -> Nat) -> Prop)
  (hQ : FluxEventOutsideCut G m cut Q)
  (hR : FluxEventOutsideCut G m cut R) :
-- imply
  BackboneLabeledSwitching.rawSourcePairFiberMass G beta J m A Q R = BackboneLabeledSwitching.rawSourcePairFiberMass G beta J m (A ∆ C) Q R := by
-- proof
  apply StatMech.Sharpness.BackboneDeterminedCutSwitching.rawSourcePairFiberMass_eq_of_determinedCutToggle G beta J m A C cut P hPsrc hPcut Q R hQ hR

/--
[actualMass_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialP2Reindex.lean)
-/
@[path]
private lemma actualMass_nil_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {beta : Real}
  {d : shb_ExplorationDomain V}
-- given
  (S : shb_PartialCurrentDynamicSelector (V := V))
  (J : Sym2 V -> Real) :
-- imply
  S.actualMass beta J d [] = currentSum d.graph beta J ∅ := by
-- proof
  apply StatMech.Sharpness.shb_PartialCurrentDynamicSelector.actualMass_nil S beta J d

/--
[pairMass_eq_of_contributingToggle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialP2Reindex.lean)
-/
@[path]
private lemma pairMass_eq_of_contributingToggle_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {A C : Finset V}
  [DecidablePred Q₁]
  [DecidablePred R₁]
  [DecidablePred Q₂]
  [DecidablePred R₂]
  {path : ContributingPathSelector G beta J A C Q₁ R₁ Q₂ R₂}
-- given
  (J : Sym2 V -> Real)
  (Q₁ R₁ Q₂ R₂ : (G.edgeFinset -> Nat) -> Prop)
  (path_sources : ∀ m hm, RandomCurrent.sources (endsM G m) (path m hm) = C)
  (transport : ∀ m hm S, (Q₁ (profileFlux G m S) ∧ R₁ (profileFlux G m (univ \ S))) <-> (Q₂ (profileFlux G m (S ∆ path m hm)) ∧ R₂ (profileFlux G m (univ \ (S ∆ path m hm)))))
  (m : G.edgeFinset -> Nat) :
-- imply
  rawSourcePairFiberMass G beta J m A Q₁ R₁ = rawSourcePairFiberMass G beta J m (A ∆ C) Q₂ R₂ := by
-- proof
  apply StatMech.Sharpness.BackbonePartialP2Reindex.pairMass_eq_of_contributingToggle G beta J A C Q₁ R₁ Q₂ R₂ path path_sources transport m

/--
[source_eq_empty_of_zero_contributes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialP2Reindex.lean)
-/
@[path]
private lemma source_eq_empty_of_zero_contributes_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {A C : Finset V}
  [DecidablePred Q₁]
  [DecidablePred R₁]
  [DecidablePred Q₂]
  [DecidablePred R₂]
  {path : ContributingPathSelector G beta J A C Q₁ R₁ Q₂ R₂}
-- given
  (J : Sym2 V -> Real)
  (Q₁ R₁ Q₂ R₂ : (G.edgeFinset -> Nat) -> Prop)
  (path_sources : ∀ m hm, RandomCurrent.sources (endsM G m) (path m hm) = C)
  (hzero : PairContributes G beta J (fun _ => 0) A C Q₁ R₁ Q₂ R₂) :
-- imply
  C = ∅ := by
-- proof
  apply StatMech.Sharpness.BackbonePartialP2Reindex.source_eq_empty_of_zero_contributes G beta J A C Q₁ R₁ Q₂ R₂ path path_sources hzero

/--
[zero_not_contributes_of_source_ne_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialP2Reindex.lean)
-/
@[path]
private lemma zero_not_contributes_of_source_ne_empty_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {A C : Finset V}
  [DecidablePred Q₁]
  [DecidablePred R₁]
  [DecidablePred Q₂]
  [DecidablePred R₂]
  {path : ContributingPathSelector G beta J A C Q₁ R₁ Q₂ R₂}
-- given
  (J : Sym2 V -> Real)
  (Q₁ R₁ Q₂ R₂ : (G.edgeFinset -> Nat) -> Prop)
  (path_sources : ∀ m hm, RandomCurrent.sources (endsM G m) (path m hm) = C)
  (hC : C ≠ ∅) :
-- imply
  ¬PairContributes G beta J (fun _ => 0) A C Q₁ R₁ Q₂ R₂ := by
-- proof
  apply StatMech.Sharpness.BackbonePartialP2Reindex.zero_not_contributes_of_source_ne_empty G beta J A C Q₁ R₁ Q₂ R₂ path path_sources hC

/--
[clearedP2_iff_pairMass_tsum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialP2Reindex.lean)
-/
@[path]
private lemma clearedP2_iff_pairMass_tsum_eq_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
  {ss : List (shb_ExplorationSegment V)}
  {A C : Finset V}
  [DecidablePred Q₁]
  [DecidablePred R₁]
  [DecidablePred Q₂]
  [DecidablePred R₂]
-- given
  (S : shb_PartialCurrentDynamicSelector (V := V))
  (J : Sym2 V -> Real)
  (Q₁ R₁ Q₂ R₂ : (d.graph.edgeFinset -> Nat) -> Prop)
  (left_reindex : S.actualMass beta J d (s :: ss) * currentSum (shb_BackboneExplorationDomain.advance d s).graph beta J ∅ = ∑' m : d.graph.edgeFinset -> Nat, rawSourcePairFiberMass d.graph beta J m A Q₁ R₁)
  (right_reindex : shb_segmentNum beta J d s * S.actualMass beta J (shb_BackboneExplorationDomain.advance d s) ss = ∑' m : d.graph.edgeFinset -> Nat, rawSourcePairFiberMass d.graph beta J m (A ∆ C) Q₂ R₂) :
-- imply
  (S.actualMass beta J d (s :: ss) * currentSum (shb_BackboneExplorationDomain.advance d s).graph beta J ∅ = shb_segmentNum beta J d s * S.actualMass beta J (shb_BackboneExplorationDomain.advance d s) ss) <-> ((∑' m : d.graph.edgeFinset -> Nat, rawSourcePairFiberMass d.graph beta J m A Q₁ R₁) = ∑' m : d.graph.edgeFinset -> Nat, rawSourcePairFiberMass d.graph beta J m (A ∆ C) Q₂ R₂) := by
-- proof
  apply StatMech.Sharpness.BackbonePartialP2Reindex.clearedP2_iff_pairMass_tsum_eq S beta J d s ss A C Q₁ R₁ Q₂ R₂ left_reindex right_reindex

/--
[actualMass_active_of_contributingToggle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialP2Reindex.lean)
-/
@[path]
private lemma actualMass_active_of_contributingToggle_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
  {ss : List (shb_ExplorationSegment V)}
  {A C : Finset V}
  [DecidablePred Q₁]
  [DecidablePred R₁]
  [DecidablePred Q₂]
  [DecidablePred R₂]
  {path : ContributingPathSelector d.graph beta J A C Q₁ R₁ Q₂ R₂}
-- given
  (S : shb_PartialCurrentDynamicSelector (V := V))
  (J : Sym2 V -> Real)
  (Q₁ R₁ Q₂ R₂ : (d.graph.edgeFinset -> Nat) -> Prop)
  (left_reindex : S.actualMass beta J d (s :: ss) * currentSum (shb_BackboneExplorationDomain.advance d s).graph beta J ∅ = ∑' m : d.graph.edgeFinset -> Nat, rawSourcePairFiberMass d.graph beta J m A Q₁ R₁)
  (right_reindex : shb_segmentNum beta J d s * S.actualMass beta J (shb_BackboneExplorationDomain.advance d s) ss = ∑' m : d.graph.edgeFinset -> Nat, rawSourcePairFiberMass d.graph beta J m (A ∆ C) Q₂ R₂)
  (path_sources : ∀ m hm, RandomCurrent.sources (endsM d.graph m) (path m hm) = C)
  (transport : ∀ m hm T, (Q₁ (profileFlux d.graph m T) ∧ R₁ (profileFlux d.graph m (univ \ T))) <-> (Q₂ (profileFlux d.graph m (T ∆ path m hm)) ∧ R₂ (profileFlux d.graph m (univ \ (T ∆ path m hm))))) :
-- imply
  S.actualMass beta J d (s :: ss) * currentSum (shb_BackboneExplorationDomain.advance d s).graph beta J ∅ = shb_segmentNum beta J d s * S.actualMass beta J (shb_BackboneExplorationDomain.advance d s) ss := by
-- proof
  apply StatMech.Sharpness.BackbonePartialP2Reindex.actualMass_active_of_contributingToggle S beta J d s ss A C Q₁ R₁ Q₂ R₂ left_reindex right_reindex path path_sources transport

/--
[actualMass_active_of_contributingDeterminedToggle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialP2Reindex.lean)
-/
@[path]
private lemma actualMass_active_of_contributingDeterminedToggle_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
  {ss : List (shb_ExplorationSegment V)}
  {A C : Finset V}
  {cut : Set (Sym2 V)}
  [DecidablePred Q]
  [DecidablePred R]
  {path : ContributingPathSelector d.graph beta J A C Q R Q R}
-- given
  (S : shb_PartialCurrentDynamicSelector (V := V))
  (J : Sym2 V -> Real)
  (Q R : (d.graph.edgeFinset -> Nat) -> Prop)
  (left_reindex : S.actualMass beta J d (s :: ss) * currentSum (shb_BackboneExplorationDomain.advance d s).graph beta J ∅ = ∑' m : d.graph.edgeFinset -> Nat, rawSourcePairFiberMass d.graph beta J m A Q R)
  (right_reindex : shb_segmentNum beta J d s * S.actualMass beta J (shb_BackboneExplorationDomain.advance d s) ss = ∑' m : d.graph.edgeFinset -> Nat, rawSourcePairFiberMass d.graph beta J m (A ∆ C) Q R)
  (path_sources : ∀ m hm, RandomCurrent.sources (endsM d.graph m) (path m hm) = C)
  (path_supported : ∀ m hm, SupportedInCut d.graph m cut (path m hm))
  (hQ : ∀ m, PairContributes d.graph beta J m A C Q R Q R -> FluxEventOutsideCut d.graph m cut Q)
  (hR : ∀ m, PairContributes d.graph beta J m A C Q R Q R -> FluxEventOutsideCut d.graph m cut R) :
-- imply
  S.actualMass beta J d (s :: ss) * currentSum (shb_BackboneExplorationDomain.advance d s).graph beta J ∅ = shb_segmentNum beta J d s * S.actualMass beta J (shb_BackboneExplorationDomain.advance d s) ss := by
-- proof
  apply StatMech.Sharpness.BackbonePartialP2Reindex.actualMass_active_of_contributingDeterminedToggle S beta J d s ss A C cut Q R left_reindex right_reindex path path_sources path_supported hQ hR

/--
[exists_contributing_of_left_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialP2Reindex.lean)
-/
@[path]
private lemma exists_contributing_of_left_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
  {ss : List (shb_ExplorationSegment V)}
  {A C : Finset V}
  [DecidablePred Q₁]
  [DecidablePred R₁]
  [DecidablePred Q₂]
  [DecidablePred R₂]
-- given
  (S : shb_PartialCurrentDynamicSelector (V := V))
  (J : Sym2 V -> Real)
  (Q₁ R₁ Q₂ R₂ : (d.graph.edgeFinset -> Nat) -> Prop)
  (left_reindex : S.actualMass beta J d (s :: ss) * currentSum (shb_BackboneExplorationDomain.advance d s).graph beta J ∅ = ∑' m : d.graph.edgeFinset -> Nat, rawSourcePairFiberMass d.graph beta J m A Q₁ R₁)
  (hleft : S.actualMass beta J d (s :: ss) * currentSum (shb_BackboneExplorationDomain.advance d s).graph beta J ∅ ≠ 0) :
-- imply
  ∃ m, PairContributes d.graph beta J m A C Q₁ R₁ Q₂ R₂ := by
-- proof
  apply StatMech.Sharpness.BackbonePartialP2Reindex.exists_contributing_of_left_ne_zero S beta J d s ss A C Q₁ R₁ Q₂ R₂ left_reindex hleft

/--
[actualMass_active_iff_pairReindex_defects_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialP2Reindex.lean)
-/
@[path]
private lemma actualMass_active_iff_pairReindex_defects_eq_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
  {ss : List (shb_ExplorationSegment V)}
  {A C : Finset V}
  [DecidablePred Q₁]
  [DecidablePred R₁]
  [DecidablePred Q₂]
  [DecidablePred R₂]
  {path : ContributingPathSelector d.graph beta J A C Q₁ R₁ Q₂ R₂}
-- given
  (S : shb_PartialCurrentDynamicSelector (V := V))
  (J : Sym2 V -> Real)
  (Q₁ R₁ Q₂ R₂ : (d.graph.edgeFinset -> Nat) -> Prop)
  (path_sources : ∀ m hm, RandomCurrent.sources (endsM d.graph m) (path m hm) = C)
  (transport : ∀ m hm T, (Q₁ (profileFlux d.graph m T) ∧ R₁ (profileFlux d.graph m (univ \ T))) <-> (Q₂ (profileFlux d.graph m (T ∆ path m hm)) ∧ R₂ (profileFlux d.graph m (univ \ (T ∆ path m hm))))) :
-- imply
  (S.actualMass beta J d (s :: ss) * currentSum (shb_BackboneExplorationDomain.advance d s).graph beta J ∅ = shb_segmentNum beta J d s * S.actualMass beta J (shb_BackboneExplorationDomain.advance d s) ss) <-> (S.actualMass beta J d (s :: ss) * currentSum (shb_BackboneExplorationDomain.advance d s).graph beta J ∅ - ∑' m : d.graph.edgeFinset -> Nat, rawSourcePairFiberMass d.graph beta J m A Q₁ R₁) = (shb_segmentNum beta J d s * S.actualMass beta J (shb_BackboneExplorationDomain.advance d s) ss - ∑' m : d.graph.edgeFinset -> Nat, rawSourcePairFiberMass d.graph beta J m (A ∆ C) Q₂ R₂) := by
-- proof
  apply StatMech.Sharpness.BackbonePartialP2Reindex.actualMass_active_iff_pairReindex_defects_eq S beta J d s ss A C Q₁ R₁ Q₂ R₂ path path_sources transport


-- created on 2026-10-23

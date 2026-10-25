/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialP2Reindex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneBondwiseOrderedExploration.Part6
import Abbrev.StatisticalMechanics.Code.Sharpness.BackbonePartialP2Reindex
open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackbonePartialP2Reindex

open FluxEdgeCopy

open BackboneLabeledSwitching

open BackboneDeterminedCutSwitching

variable {D : Type*}

theorem pairMass_eq_of_contributingToggle
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (A C : Finset V)
    (Q₁ R₁ Q₂ R₂ : (G.edgeFinset -> Nat) -> Prop)
    [DecidablePred Q₁] [DecidablePred R₁]
    [DecidablePred Q₂] [DecidablePred R₂]
    (path : ContributingPathSelector G beta J A C Q₁ R₁ Q₂ R₂)
    (path_sources : ∀ m hm,
      RandomCurrent.sources (endsM G m) (path m hm) = C)
    (transport : ∀ m hm S,
      (Q₁ (profileFlux G m S) ∧
          R₁ (profileFlux G m (univ \ S))) <->
        (Q₂ (profileFlux G m (S ∆ path m hm)) ∧
          R₂ (profileFlux G m (univ \ (S ∆ path m hm)))))
    (m : G.edgeFinset -> Nat) :
    rawSourcePairFiberMass G beta J m A Q₁ R₁ =
      rawSourcePairFiberMass G beta J m (A ∆ C) Q₂ R₂ := by
  by_cases hm : PairContributes G beta J m A C Q₁ R₁ Q₂ R₂
  · exact rawSourcePairFiberMass_eq_of_labeledToggle G beta J m A C
      (path m hm) (path_sources m hm) Q₁ R₁ Q₂ R₂ (transport m hm)
  · unfold PairContributes at hm
    rw [not_or] at hm
    exact (not_ne_iff.mp hm.1).trans (not_ne_iff.mp hm.2).symm


theorem source_eq_empty_of_zero_contributes
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (A C : Finset V)
    (Q₁ R₁ Q₂ R₂ : (G.edgeFinset -> Nat) -> Prop)
    [DecidablePred Q₁] [DecidablePred R₁]
    [DecidablePred Q₂] [DecidablePred R₂]
    (path : ContributingPathSelector G beta J A C Q₁ R₁ Q₂ R₂)
    (path_sources : ∀ m hm,
      RandomCurrent.sources (endsM G m) (path m hm) = C)
    (hzero : PairContributes G beta J (fun _ => 0)
      A C Q₁ R₁ Q₂ R₂) :
    C = ∅ := by
  let m0 : G.edgeFinset -> Nat := fun _ => 0
  have hcopies : path m0 hzero = ∅ := by
    ext i
    exact Fin.elim0 i.2
  calc
    C = RandomCurrent.sources (endsM G m0) (path m0 hzero) :=
      (path_sources m0 hzero).symm
    _ = RandomCurrent.sources (endsM G m0) ∅ := by rw [hcopies]
    _ = ∅ := by
      ext v
      simp [RandomCurrent.mem_sources, RandomCurrent.degK]


theorem zero_not_contributes_of_source_ne_empty
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (A C : Finset V)
    (Q₁ R₁ Q₂ R₂ : (G.edgeFinset -> Nat) -> Prop)
    [DecidablePred Q₁] [DecidablePred R₁]
    [DecidablePred Q₂] [DecidablePred R₂]
    (path : ContributingPathSelector G beta J A C Q₁ R₁ Q₂ R₂)
    (path_sources : ∀ m hm,
      RandomCurrent.sources (endsM G m) (path m hm) = C)
    (hC : C ≠ ∅) :
    ¬PairContributes G beta J (fun _ => 0) A C Q₁ R₁ Q₂ R₂ := by
  intro hzero
  exact hC (source_eq_empty_of_zero_contributes G beta J A C
    Q₁ R₁ Q₂ R₂ path path_sources hzero)


theorem clearedP2_iff_pairMass_tsum_eq
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V))
    (A C : Finset V)
    (Q₁ R₁ Q₂ R₂ : (d.graph.edgeFinset -> Nat) -> Prop)
    [DecidablePred Q₁] [DecidablePred R₁]
    [DecidablePred Q₂] [DecidablePred R₂]
    (left_reindex :
      S.actualMass beta J d (s :: ss) *
          currentSum (shb_BackboneExplorationDomain.advance d s).graph
            beta J ∅ =
        ∑' m : d.graph.edgeFinset -> Nat,
          rawSourcePairFiberMass d.graph beta J m A Q₁ R₁)
    (right_reindex :
      shb_segmentNum beta J d s *
          S.actualMass beta J
            (shb_BackboneExplorationDomain.advance d s) ss =
        ∑' m : d.graph.edgeFinset -> Nat,
          rawSourcePairFiberMass d.graph beta J m (A ∆ C) Q₂ R₂) :
    (S.actualMass beta J d (s :: ss) *
          currentSum (shb_BackboneExplorationDomain.advance d s).graph
            beta J ∅ =
        shb_segmentNum beta J d s *
          S.actualMass beta J
            (shb_BackboneExplorationDomain.advance d s) ss) <->
      ((∑' m : d.graph.edgeFinset -> Nat,
          rawSourcePairFiberMass d.graph beta J m A Q₁ R₁) =
        ∑' m : d.graph.edgeFinset -> Nat,
          rawSourcePairFiberMass d.graph beta J m (A ∆ C) Q₂ R₂) := by
  rw [left_reindex, right_reindex]


theorem actualMass_active_of_contributingToggle
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V))
    (A C : Finset V)
    (Q₁ R₁ Q₂ R₂ : (d.graph.edgeFinset -> Nat) -> Prop)
    [DecidablePred Q₁] [DecidablePred R₁]
    [DecidablePred Q₂] [DecidablePred R₂]
    (left_reindex :
      S.actualMass beta J d (s :: ss) *
          currentSum (shb_BackboneExplorationDomain.advance d s).graph
            beta J ∅ =
        ∑' m : d.graph.edgeFinset -> Nat,
          rawSourcePairFiberMass d.graph beta J m A Q₁ R₁)
    (right_reindex :
      shb_segmentNum beta J d s *
          S.actualMass beta J
            (shb_BackboneExplorationDomain.advance d s) ss =
        ∑' m : d.graph.edgeFinset -> Nat,
          rawSourcePairFiberMass d.graph beta J m (A ∆ C) Q₂ R₂)
    (path : ContributingPathSelector d.graph beta J A C Q₁ R₁ Q₂ R₂)
    (path_sources : ∀ m hm,
      RandomCurrent.sources (endsM d.graph m) (path m hm) = C)
    (transport : ∀ m hm T,
      (Q₁ (profileFlux d.graph m T) ∧
          R₁ (profileFlux d.graph m (univ \ T))) <->
        (Q₂ (profileFlux d.graph m (T ∆ path m hm)) ∧
          R₂ (profileFlux d.graph m (univ \ (T ∆ path m hm))))) :
    S.actualMass beta J d (s :: ss) *
        currentSum (shb_BackboneExplorationDomain.advance d s).graph
          beta J ∅ =
      shb_segmentNum beta J d s *
        S.actualMass beta J
          (shb_BackboneExplorationDomain.advance d s) ss := by
  rw [left_reindex, right_reindex]
  apply tsum_congr
  exact pairMass_eq_of_contributingToggle d.graph beta J A C
    Q₁ R₁ Q₂ R₂ path path_sources transport


theorem actualMass_active_of_contributingDeterminedToggle
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V))
    (A C : Finset V) (cut : Set (Sym2 V))
    (Q R : (d.graph.edgeFinset -> Nat) -> Prop)
    [DecidablePred Q] [DecidablePred R]
    (left_reindex :
      S.actualMass beta J d (s :: ss) *
          currentSum (shb_BackboneExplorationDomain.advance d s).graph
            beta J ∅ =
        ∑' m : d.graph.edgeFinset -> Nat,
          rawSourcePairFiberMass d.graph beta J m A Q R)
    (right_reindex :
      shb_segmentNum beta J d s *
          S.actualMass beta J
            (shb_BackboneExplorationDomain.advance d s) ss =
        ∑' m : d.graph.edgeFinset -> Nat,
          rawSourcePairFiberMass d.graph beta J m (A ∆ C) Q R)
    (path : ContributingPathSelector d.graph beta J A C Q R Q R)
    (path_sources : ∀ m hm,
      RandomCurrent.sources (endsM d.graph m) (path m hm) = C)
    (path_supported : ∀ m hm,
      SupportedInCut d.graph m cut (path m hm))
    (hQ : ∀ m, PairContributes d.graph beta J m A C Q R Q R ->
      FluxEventOutsideCut d.graph m cut Q)
    (hR : ∀ m, PairContributes d.graph beta J m A C Q R Q R ->
      FluxEventOutsideCut d.graph m cut R) :
    S.actualMass beta J d (s :: ss) *
        currentSum (shb_BackboneExplorationDomain.advance d s).graph
          beta J ∅ =
      shb_segmentNum beta J d s *
        S.actualMass beta J
          (shb_BackboneExplorationDomain.advance d s) ss := by
  apply actualMass_active_of_contributingToggle S beta J d s ss A C
    Q R Q R left_reindex right_reindex path path_sources
  intro m hm T
  exact pairTransport_of_fluxEventsOutsideCut d.graph m cut Q R
    (hQ m hm) (hR m hm) (path m hm) (path_supported m hm) T


theorem exists_contributing_of_left_ne_zero
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V))
    (A C : Finset V)
    (Q₁ R₁ Q₂ R₂ : (d.graph.edgeFinset -> Nat) -> Prop)
    [DecidablePred Q₁] [DecidablePred R₁]
    [DecidablePred Q₂] [DecidablePred R₂]
    (left_reindex :
      S.actualMass beta J d (s :: ss) *
          currentSum (shb_BackboneExplorationDomain.advance d s).graph
            beta J ∅ =
        ∑' m : d.graph.edgeFinset -> Nat,
          rawSourcePairFiberMass d.graph beta J m A Q₁ R₁)
    (hleft : S.actualMass beta J d (s :: ss) *
        currentSum (shb_BackboneExplorationDomain.advance d s).graph
          beta J ∅ ≠ 0) :
    ∃ m, PairContributes d.graph beta J m A C Q₁ R₁ Q₂ R₂ := by
  by_contra hnone
  push Not at hnone
  have hzero : (∑' m : d.graph.edgeFinset -> Nat,
      rawSourcePairFiberMass d.graph beta J m A Q₁ R₁) = 0 := by
    rw [show (fun m : d.graph.edgeFinset -> Nat =>
        rawSourcePairFiberMass d.graph beta J m A Q₁ R₁) =
          (fun _ => 0) by
      funext m
      exact not_ne_iff.mp (not_or.mp (hnone m)).1]
    exact tsum_zero
  exact hleft (left_reindex.trans hzero)


theorem actualMass_active_iff_pairReindex_defects_eq
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V))
    (A C : Finset V)
    (Q₁ R₁ Q₂ R₂ : (d.graph.edgeFinset -> Nat) -> Prop)
    [DecidablePred Q₁] [DecidablePred R₁]
    [DecidablePred Q₂] [DecidablePred R₂]
    (path : ContributingPathSelector d.graph beta J A C Q₁ R₁ Q₂ R₂)
    (path_sources : ∀ m hm,
      RandomCurrent.sources (endsM d.graph m) (path m hm) = C)
    (transport : ∀ m hm T,
      (Q₁ (profileFlux d.graph m T) ∧
          R₁ (profileFlux d.graph m (univ \ T))) <->
        (Q₂ (profileFlux d.graph m (T ∆ path m hm)) ∧
          R₂ (profileFlux d.graph m (univ \ (T ∆ path m hm))))) :
    (S.actualMass beta J d (s :: ss) *
          currentSum (shb_BackboneExplorationDomain.advance d s).graph
            beta J ∅ =
        shb_segmentNum beta J d s *
          S.actualMass beta J
            (shb_BackboneExplorationDomain.advance d s) ss) <->
      (S.actualMass beta J d (s :: ss) *
          currentSum (shb_BackboneExplorationDomain.advance d s).graph
            beta J ∅ -
        ∑' m : d.graph.edgeFinset -> Nat,
          rawSourcePairFiberMass d.graph beta J m A Q₁ R₁) =
      (shb_segmentNum beta J d s *
          S.actualMass beta J
            (shb_BackboneExplorationDomain.advance d s) ss -
        ∑' m : d.graph.edgeFinset -> Nat,
          rawSourcePairFiberMass d.graph beta J m (A ∆ C) Q₂ R₂) := by
  let left := S.actualMass beta J d (s :: ss) *
    currentSum (shb_BackboneExplorationDomain.advance d s).graph beta J ∅
  let right := shb_segmentNum beta J d s *
    S.actualMass beta J (shb_BackboneExplorationDomain.advance d s) ss
  let leftSum := ∑' m : d.graph.edgeFinset -> Nat,
    rawSourcePairFiberMass d.graph beta J m A Q₁ R₁
  let rightSum := ∑' m : d.graph.edgeFinset -> Nat,
    rawSourcePairFiberMass d.graph beta J m (A ∆ C) Q₂ R₂
  have hsum : leftSum = rightSum := by
    apply tsum_congr
    exact pairMass_eq_of_contributingToggle d.graph beta J A C
      Q₁ R₁ Q₂ R₂ path path_sources transport
  change left = right <-> left - leftSum = right - rightSum
  constructor
  · intro hlr
    linarith
  · intro hdefect
    linarith

end BackbonePartialP2Reindex
end
end StatMech.Sharpness

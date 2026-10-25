/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Abbrev.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part6
open Finset


namespace StatMech.GrahamGHS.FourColor

universe u v uI uW

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


attribute [instance]
  FiniteRelationMinimalTightProblem.stateFintype
  FiniteRelationMinimalTightProblem.stateDecidableEq
  FiniteRelationMinimalTightProblem.tokenFintype
  FiniteRelationMinimalTightProblem.tokenDecidableEq

noncomputable def canonicalStableRawComponentReferenceStepBelowRankEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (rankBound : Nat) :
    CanonicalStableRawComponentSelfBelowRank
        ends m j k l zero hloop hjk hkl hk0 p hno component rankBound ↪
      (CanonicalStableRawComponentDirectBelowRank
          ends m j k l zero hloop hjk hkl hk0 p hno component rankBound ⊕
        CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  let step := canonicalStableRawComponentReferenceStepEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let f : CanonicalStableRawComponentSelfBelowRank
        ends m j k l zero hloop hjk hkl hk0 p hno component rankBound →
      (CanonicalStableRawComponentDirectBelowRank
          ends m j k l zero hloop hjk hkl hk0 p hno component rankBound ⊕
        CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) := fun self =>
    match hstep : step self.1 with
    | Sum.inl direct => Sum.inl ⟨direct, by
        have hrank :=
          canonicalStableRawComponentReferenceStepEmbedding_inl_rank_lt
            ends m j k l zero hloop hjk hkl hk0 p hno component
              self.1 direct hstep
        exact hrank.trans self.2⟩
    | Sum.inr terminal => Sum.inr terminal
  have hrecover (self : CanonicalStableRawComponentSelfBelowRank
      ends m j k l zero hloop hjk hkl hk0 p hno component rankBound) :
      Sum.map (fun direct => direct.1) id (f self) = step self.1 := by
    unfold f
    split
    next direct hstep => simpa only [Sum.map] using hstep.symm
    next terminal hstep => simpa only [Sum.map] using hstep.symm
  refine ⟨f, ?_⟩
  intro self other heq
  apply Subtype.ext
  apply step.injective
  calc
    step self.1 = Sum.map (fun direct => direct.1) id (f self) :=
      (hrecover self).symm
    _ = Sum.map (fun direct => direct.1) id (f other) := congrArg _ heq
    _ = step other.1 := hrecover other


end StatMech.GrahamGHS.FourColor

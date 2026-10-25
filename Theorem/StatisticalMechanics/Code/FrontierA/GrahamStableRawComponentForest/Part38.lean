/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part38
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

theorem canonicalStableRawComponentReferenceChildren_rank_lt
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (self child : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hchild : child ∈ canonicalStableRawComponentReferenceChildren
      ends m j k l zero hloop hjk hkl hk0 p hno component self) :
    canonicalStableRawComponentSelfRank
        ends m j k l zero hloop hjk hkl hk0 p hno component child <
      canonicalStableRawComponentSelfRank
        ends m j k l zero hloop hjk hkl hk0 p hno component self := by
  classical
  unfold canonicalStableRawComponentReferenceChildren at hchild
  obtain ⟨direct, hstep, collision, hcollisionSelf, hcollisionDirect⟩ :=
    (Finset.mem_filter.mp hchild).2
  have hrank :=
    canonicalStableRawComponentReferenceStepEmbedding_inl_rank_lt
      ends m j k l zero hloop hjk hkl hk0 p hno component
        self direct hstep
  have hsource := canonicalStableRawComponentCrossCollision_source_eq_direct
    ends m j k l zero hloop hjk hkl hk0 p hno component collision
  unfold canonicalStableRawComponentSelfRank
  rw [← hcollisionSelf, hsource, hcollisionDirect]
  exact hrank


end StatMech.GrahamGHS.FourColor

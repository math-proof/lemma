/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part27
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

theorem canonicalStableRawComponentReferenceStepEmbedding_inl_rank_lt
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (self : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (direct : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hstep : canonicalStableRawComponentReferenceStepEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component self =
      Sum.inl direct) :
    canonicalStableRawSourceRank ends m j k l zero p direct.1.source <
      canonicalStableRawSourceRank ends m j k l zero p self.1.source := by
  classical
  let tokenEquiv :=
    canonicalStableRawComponentDirectSumNonexceptionalEquivToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
  have htokenComponent := congrArg tokenEquiv hstep
  change tokenEquiv (tokenEquiv.symm
      (canonicalStableRawComponentReferenceOwnerEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component self)) =
    tokenEquiv (Sum.inl direct) at htokenComponent
  rw [tokenEquiv.apply_symm_apply] at htokenComponent
  have htoken := congrArg Subtype.val htokenComponent
  change (canonicalStableRawComponentAlternateToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
        ⟨self.1, self.2.1⟩).1 =
    canonicalStableRawStateLeftToken
      ends m j k l zero hloop hjk hkl hk0 p hno direct.1 at htoken
  unfold canonicalStableRawComponentAlternateToken
    canonicalStableRawStateLeftToken at htoken
  rw [dif_pos self.2.2, dif_neg direct.2.2] at htoken
  have hsource : direct.1.source =
      (canonicalStableRawReferenceOwnerLeftToken
        ends m j k l zero hloop hjk hkl hk0 p self.1 self.2.2).1 :=
    (congrArg Sigma.fst htoken).symm
  rw [hsource]
  exact canonicalStableRawReferenceOwnerLeftToken_rank_lt
    ends m j k l zero hloop hjk hkl hk0 p self.1 self.2.2


end StatMech.GrahamGHS.FourColor

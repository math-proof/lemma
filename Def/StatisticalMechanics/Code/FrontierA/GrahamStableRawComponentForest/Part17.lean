/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Abbrev.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part5
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

noncomputable def canonicalStableRawComponentDirectStateEquivExceptionalToken
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component ≃
      CanonicalStableRawComponentExceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component := by
  classical
  let directMap := canonicalStableRawComponentDirectEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let f : CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component →
      CanonicalStableRawComponentExceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component := fun direct =>
    ⟨directMap direct, by
      change CanonicalStableRawLeftTokenIsExceptional
        ends m j k l zero hloop hjk hkl hk0 p
          (canonicalStableRawStateLeftToken
            ends m j k l zero hloop hjk hkl hk0 p hno direct.1)
      unfold canonicalStableRawStateLeftToken
      rw [dif_neg direct.2.2]
      exact canonicalStableRawDirectLeftToken_isExceptional
        ends m j k l zero hloop hjk hkl hk0 p direct.1 direct.2.2⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    apply directMap.injective
    exact congrArg Subtype.val hxy
  · intro token
    let raw := token.1.1
    let edge := canonicalStableRawExceptionalEdgeOfLeftToken
      ends m j k l zero hloop hjk hkl hk0 p raw token.2
    have hdirect : edge.target.1 ≠ canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p edge.source := by
      exact Finset.ne_of_mem_erase raw.2.2
    have hcomponent : canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno edge = component := by
      exact (canonicalStableRawLeftToken_fullComponent_of_stateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p hno raw edge
          (canonicalStableRawExceptionalLeftToken_stateTokenIncidence
            ends m j k l zero hloop hjk hkl hk0 p raw token.2)).symm.trans
        token.1.2
    let direct : CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨edge, hcomponent, hdirect⟩
    refine ⟨direct, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno direct.1 = raw
    unfold canonicalStableRawStateLeftToken
    rw [dif_neg direct.2.2]
    unfold direct edge raw canonicalStableRawDirectLeftToken
      canonicalStableRawExceptionalEdgeOfLeftToken
      canonicalStableRawLeftTokenTarget
    rfl

end StatMech.GrahamGHS.FourColor

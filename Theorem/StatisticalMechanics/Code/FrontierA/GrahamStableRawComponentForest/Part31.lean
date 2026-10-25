/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part30
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

theorem canonicalStableRawComponentPreferredDirectStep_inl_next
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (direct next : CanonicalStableRawComponentPreferredDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hstep : canonicalStableRawComponentPreferredDirectStep
        ends m j k l zero hloop hjk hkl hk0 p hno component direct =
      Sum.inl next) :
    next.1.1 = canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno direct.1.1 := by
  classical
  unfold canonicalStableRawComponentPreferredDirectStep at hstep
  dsimp only at hstep
  split at hstep
  next hnextPreferred =>
    exact congrArg (fun state => state.1.1) (Sum.inl.inj hstep).symm
  next _ => contradiction

theorem canonicalStableRawComponentPreferredDirectAdvance_eq_of_step
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (direct next : CanonicalStableRawComponentPreferredDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hstep : canonicalStableRawComponentPreferredDirectStep
        ends m j k l zero hloop hjk hkl hk0 p hno component direct =
      Sum.inl next) :
    partialForestAdvance
        (canonicalStableRawComponentPreferredDirectStep
          ends m j k l zero hloop hjk hkl hk0 p hno component) direct =
      next := by
  unfold partialForestAdvance
  rw [hstep]


theorem
    canonicalStableRawComponentSecondAlternateFiber_terminal_or_preferredSelfOutput
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (anchor : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p terminal.1.1 =
        canonicalStableRawComponentSecondAlternateTarget
          ends m j k l zero hloop hjk hkl hk0 p hno component anchor) ∨
      ∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        u.target = canonicalStableRawComponentSecondAlternateTarget
          ends m j k l zero hloop hjk hkl hk0 p hno component anchor ∧
        (CanonicalStableRawOwnerStableOutput
            ends m j k l zero hloop hjk hkl hk0 p anchor.1.2.1 u ∨
          CanonicalStableRawOwnerAdvancingOutput
            ends m j k l zero hloop hjk hkl hk0 p anchor.1.2.1 u) ∧
        canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧
        (canonicalStableRawComponentSecondAlternateTarget
          ends m j k l zero hloop hjk hkl hk0 p hno component anchor).1 =
          canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
            ⟨canonicalStableRawPreferredRightBase ends m j k l zero
                hloop hjk hkl hk0 p
                  (canonicalStableRawComponentSecondAlternateTarget
                    ends m j k l zero hloop hjk hkl hk0 p hno component anchor),
              canonicalStableRawPreferredRightBase_mem ends m j k l zero
                hloop hjk hkl hk0 p
                  (canonicalStableRawComponentSecondAlternateTarget
                    ends m j k l zero hloop hjk hkl hk0 p hno component anchor)⟩ := by
  classical
  let target := canonicalStableRawComponentSecondAlternateTarget
    ends m j k l zero hloop hjk hkl hk0 p hno component anchor
  let owner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p target,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p target⟩
  by_cases hfree : target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p owner
  · exact Or.inl
      (exists_canonicalStableRawComponentSecondAlternateFiber_freeTerminal
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor hfree)
  · obtain ⟨u, huTarget, huKind, huComponent⟩ :=
      canonicalStableRawComponentSecondCollisionAlternateToken_outputDichotomy
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor
    exact Or.inr ⟨u, huTarget, huKind, huComponent,
      Classical.not_not.mp hfree⟩


theorem
    canonicalStableRawComponentSecondAlternatePreferredSelfOutput_stepSplit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (anchor : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hpreferredSelf :
      (canonicalStableRawComponentSecondAlternateTarget
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor).1 =
        canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
          ⟨canonicalStableRawPreferredRightBase ends m j k l zero
              hloop hjk hkl hk0 p
                (canonicalStableRawComponentSecondAlternateTarget
                  ends m j k l zero hloop hjk hkl hk0 p hno component anchor),
            canonicalStableRawPreferredRightBase_mem ends m j k l zero
              hloop hjk hkl hk0 p
                (canonicalStableRawComponentSecondAlternateTarget
                  ends m j k l zero hloop hjk hkl hk0 p hno component anchor)⟩) :
    (∃ self : CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          self.1.target = canonicalStableRawComponentSecondAlternateTarget
            ends m j k l zero hloop hjk hkl hk0 p hno component anchor ∧
          canonicalStableRawComponentReferenceStepEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component self =
            Sum.inr terminal) ∨
      (∃ self : CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        ∃ direct : CanonicalStableRawComponentDirectState
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          self.1.target = canonicalStableRawComponentSecondAlternateTarget
            ends m j k l zero hloop hjk hkl hk0 p hno component anchor ∧
          canonicalStableRawComponentReferenceStepEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component self =
            Sum.inl direct ∧
          canonicalStableRawSourceRank ends m j k l zero p direct.1.source <
            canonicalStableRawSourceRank ends m j k l zero p self.1.source) ∨
      ∃ direct : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        direct.1.target = canonicalStableRawComponentSecondAlternateTarget
          ends m j k l zero hloop hjk hkl hk0 p hno component anchor ∧
        (CanonicalStableRawOwnerStableOutput
            ends m j k l zero hloop hjk hkl hk0 p anchor.1.2.1 direct.1 ∨
          CanonicalStableRawOwnerAdvancingOutput
            ends m j k l zero hloop hjk hkl hk0 p anchor.1.2.1 direct.1) ∧
        (canonicalStableRawComponentSecondAlternateTarget
          ends m j k l zero hloop hjk hkl hk0 p hno component anchor).1 =
          canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
            ⟨canonicalStableRawPreferredRightBase ends m j k l zero
                hloop hjk hkl hk0 p
                  (canonicalStableRawComponentSecondAlternateTarget
                    ends m j k l zero hloop hjk hkl hk0 p hno component anchor),
              canonicalStableRawPreferredRightBase_mem ends m j k l zero
                hloop hjk hkl hk0 p
                  (canonicalStableRawComponentSecondAlternateTarget
                    ends m j k l zero hloop hjk hkl hk0 p hno component anchor)⟩ := by
  classical
  obtain ⟨u, huTarget, huKind, huComponent⟩ :=
    canonicalStableRawComponentSecondCollisionAlternateToken_outputDichotomy
      ends m j k l zero hloop hjk hkl hk0 p hno component anchor
  by_cases hself : u.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p u.source
  · let self : CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨u, huComponent, hself⟩
    cases hstep : canonicalStableRawComponentReferenceStepEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component self with
    | inl direct =>
        exact Or.inr (Or.inl ⟨self, direct, huTarget,
          hstep,
          canonicalStableRawComponentReferenceStepEmbedding_inl_rank_lt
            ends m j k l zero hloop hjk hkl hk0 p hno component
              self direct hstep⟩)
    | inr terminal =>
        exact Or.inl ⟨self, terminal, huTarget, hstep⟩
  · let direct : CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨u, huComponent, hself⟩
    exact Or.inr (Or.inr
      ⟨direct, huTarget, huKind, hpreferredSelf⟩)


theorem
    canonicalStableRawComponentSecondAlternateFreeFiberRepresentativesEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (A : Finset (StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)))
    (hfree : ∀ anchor ∈ A,
      (canonicalStableRawComponentSecondAlternateTarget
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor).1 ≠
      canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p
          ⟨canonicalStableRawPreferredRightBase ends m j k l zero
              hloop hjk hkl hk0 p
                (canonicalStableRawComponentSecondAlternateTarget
                  ends m j k l zero hloop hjk hkl hk0 p hno component anchor),
            canonicalStableRawPreferredRightBase_mem ends m j k l zero
              hloop hjk hkl hk0 p
                (canonicalStableRawComponentSecondAlternateTarget
                  ends m j k l zero hloop hjk hkl hk0 p hno component anchor)⟩)
    (htarget : Function.Injective fun anchor : ↑A =>
      canonicalStableRawComponentSecondAlternateTarget
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor.1) :
    Nonempty (↑A ↪ CanonicalStableRawComponentNonexceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  have hexists (anchor : ↑A) :
      ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawLeftTokenTarget
            ends m j k l zero hloop hjk hkl hk0 p terminal.1.1 =
          canonicalStableRawComponentSecondAlternateTarget
            ends m j k l zero hloop hjk hkl hk0 p hno component anchor.1 :=
    exists_canonicalStableRawComponentSecondAlternateFiber_freeTerminal
      ends m j k l zero hloop hjk hkl hk0 p hno component anchor.1
        (hfree anchor.1 anchor.2)
  let f : ↑A → CanonicalStableRawComponentNonexceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component := fun anchor =>
    Classical.choose (hexists anchor)
  have hfTarget (anchor : ↑A) :
      canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p (f anchor).1.1 =
        canonicalStableRawComponentSecondAlternateTarget
          ends m j k l zero hloop hjk hkl hk0 p hno component anchor.1 :=
    Classical.choose_spec (hexists anchor)
  refine ⟨⟨f, ?_⟩⟩
  intro x y hxy
  apply htarget
  calc
    canonicalStableRawComponentSecondAlternateTarget
        ends m j k l zero hloop hjk hkl hk0 p hno component x.1 =
      canonicalStableRawLeftTokenTarget
        ends m j k l zero hloop hjk hkl hk0 p (f x).1.1 := (hfTarget x).symm
    _ = canonicalStableRawLeftTokenTarget
        ends m j k l zero hloop hjk hkl hk0 p (f y).1.1 := congrArg
          (fun terminal : CanonicalStableRawComponentNonexceptionalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component =>
              canonicalStableRawLeftTokenTarget
                ends m j k l zero hloop hjk hkl hk0 p terminal.1.1) hxy
    _ = canonicalStableRawComponentSecondAlternateTarget
        ends m j k l zero hloop hjk hkl hk0 p hno component y.1 :=
      hfTarget y


end StatMech.GrahamGHS.FourColor

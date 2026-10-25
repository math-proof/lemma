/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute.Part31
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalStableRawComponentNaturalToken_incident
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (s : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component s
        (canonicalStableRawComponentNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component s) := by
  apply (canonicalStableRawWitnessedStateTokenIncidence_iff
    ends m j k l zero hloop hjk hkl hk0 p _ _).2
  exact canonicalStableRawStateLeftToken_stateTokenIncidence
    ends m j k l zero hloop hjk hkl hk0 p hno s.1


theorem exists_canonicalStableRawComponentPartialMatching_saturating
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    let State :=
      {s : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p //
        canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno s = component}
    let Token :=
      {token : CanonicalStableRawLeftSurplusToken
          ends m j k l zero hloop hjk hkl hk0 p //
        canonicalStableRawFullLeftTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno token = component}
    let incident : State -> Token -> Prop := fun s token =>
      CanonicalStableRawWitnessedStateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p token.1 s.1
    ∃ matching : StatMech.FrontierA.RelationPartialMatching incident,
      matching.IsMaximum ∧
        ∀ s, s ∉ matching.support ->
          ∃ t, matching.toFun t = some
            (⟨canonicalStableRawStateLeftToken
                  ends m j k l zero hloop hjk hkl hk0 p hno s.1,
              (canonicalStableRawStateLeftToken_fullComponent
                ends m j k l zero hloop hjk hkl hk0 p hno s.1).trans s.2⟩ :
              Token) := by
  classical
  dsimp only
  let State :=
    {s : CanonicalStableRawExceptionalEdge
        ends m j k l zero hloop hjk hkl hk0 p //
      canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno s = component}
  let Token :=
    {token : CanonicalStableRawLeftSurplusToken
        ends m j k l zero hloop hjk hkl hk0 p //
      canonicalStableRawFullLeftTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno token = component}
  let incident : State -> Token -> Prop := fun s token =>
    CanonicalStableRawWitnessedStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p token.1 s.1
  obtain ⟨matching, hmaximum, hsaturates⟩ :=
    StatMech.FrontierA.exists_relationPartialMatching_saturating_unmatched
      incident
  refine ⟨matching, hmaximum, ?_⟩
  intro s hs
  let naturalToken : Token :=
    ⟨canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s.1,
      (canonicalStableRawStateLeftToken_fullComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s.1).trans s.2⟩
  exact hsaturates s hs naturalToken
    ((canonicalStableRawWitnessedStateTokenIncidence_iff
      ends m j k l zero hloop hjk hkl hk0 p naturalToken.1 s.1).2
      (canonicalStableRawStateLeftToken_stateTokenIncidence
          ends m j k l zero hloop hjk hkl hk0 p hno s.1))


theorem canonicalStableRawComponentHoleMove_classification
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (state : StatMech.FrontierA.RelationPartialMatching.HoleState
      (CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    let natural := canonicalStableRawComponentNaturalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let hnatural := canonicalStableRawComponentNaturalToken_incident
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let moved := state.move natural hnatural
    state.hole ≠ moved.hole ∧
      ∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        u.target = canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p (natural state.hole).1 ∧
        (CanonicalStableRawOwnerStableOutput
            ends m j k l zero hloop hjk hkl hk0 p state.hole.1 u ∨
          CanonicalStableRawOwnerAdvancingOutput
            ends m j k l zero hloop hjk hkl hk0 p state.hole.1 u) ∧
        canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
  classical
  dsimp only
  let natural := canonicalStableRawComponentNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let hnatural := canonicalStableRawComponentNaturalToken_incident
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let moved := state.move natural hnatural
  have hoccupied : state.matching.toFun moved.hole =
      some (natural state.hole) := by
    exact state.matching_apply_move_hole natural hnatural
  have hne : state.hole ≠ moved.hole := by
    intro h
    apply state.hole_unmatched
    apply (StatMech.FrontierA.RelationPartialMatching.mem_support_iff
      state.matching state.hole).2
    exact ⟨natural state.hole, h ▸ hoccupied⟩
  have hs : CanonicalStableRawWitnessedStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p
        (natural state.hole).1 state.hole.1 := hnatural state.hole
  have ht : CanonicalStableRawWitnessedStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p
        (natural state.hole).1 moved.hole.1 :=
    state.matching.related hoccupied
  have hclassify :=
    canonicalStableRawWitnessedStateTokenIncidence_sharedTokenClassification
      ends m j k l zero hloop hjk hkl hk0 p hno
        (natural state.hole).1 state.hole.1 moved.hole.1 hs ht
  refine ⟨hne, ?_⟩
  rcases hclassify with heq | hstable | hadvancing
  · exact False.elim (hne (Subtype.ext heq))
  · obtain ⟨u, huTarget, huStable, huComponent, _⟩ := hstable
    exact ⟨u, huTarget, Or.inl huStable, huComponent.trans state.hole.2⟩
  · obtain ⟨u, huTarget, huAdvancing, huComponent, _⟩ := hadvancing
    exact ⟨u, huTarget, Or.inr huAdvancing, huComponent.trans state.hole.2⟩


theorem exists_canonicalStableRawComponentCrossCollision_of_card_lt
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (hcard : Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) <
        Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    let selfMap := canonicalStableRawComponentSelfEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let directMap := canonicalStableRawComponentDirectEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let incident := CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let natural := canonicalStableRawComponentNaturalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let hnatural := canonicalStableRawComponentNaturalToken_incident
      ends m j k l zero hloop hjk hkl hk0 p hno component
    ∃ state : StatMech.FrontierA.RelationPartialMatching.HoleState incident,
      ∃ collision : StatMech.FrontierA.crossCollision selfMap directMap,
        state.hole.1 = collision.1.1.1 ∧
          (state.move natural hnatural).hole.1 = collision.1.2.1 := by
  classical
  dsimp only
  let selfMap := canonicalStableRawComponentSelfEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let directMap := canonicalStableRawComponentDirectEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let incident := CanonicalStableRawComponentIncident
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let natural := canonicalStableRawComponentNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let hnatural := canonicalStableRawComponentNaturalToken_incident
    ends m j k l zero hloop hjk hkl hk0 p hno component
  obtain ⟨state, hholes, htoken⟩ :=
    StatMech.FrontierA.RelationPartialMatching.exists_maximalNatural_holeState_collision
      incident natural hnatural hcard
  have hrawToken : canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno state.hole.1 =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno
          (state.move natural hnatural).hole.1 := by
    exact congrArg Subtype.val htoken
  rcases canonicalStableRawStateLeftToken_eq_imp
      ends m j k l zero hloop hjk hkl hk0 p hno
        state.hole.1 (state.move natural hnatural).hole.1 hrawToken with
    heq | hforward | hreverse
  · exact False.elim (hholes (Subtype.ext heq))
  · let self : CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component :=
        ⟨state.hole.1, state.hole.2, hforward.1⟩
    let direct : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component :=
        ⟨(state.move natural hnatural).hole.1,
          (state.move natural hnatural).hole.2, hforward.2.1⟩
    let collision : StatMech.FrontierA.crossCollision selfMap directMap :=
      ⟨(self, direct), by
        apply Subtype.ext
        exact hrawToken⟩
    exact ⟨state, collision, rfl, rfl⟩
  · let self : CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component :=
        ⟨(state.move natural hnatural).hole.1,
          (state.move natural hnatural).hole.2, hreverse.1⟩
    let direct : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component :=
        ⟨state.hole.1, state.hole.2, hreverse.2.1⟩
    let collision : StatMech.FrontierA.crossCollision selfMap directMap :=
      ⟨(self, direct), by
        apply Subtype.ext
        exact hrawToken.symm⟩
    have hback := state.move_move_hole_eq_of_natural_eq
      natural hnatural htoken
    refine ⟨state.move natural hnatural, collision, rfl, ?_⟩
    exact congrArg Subtype.val hback


end StatMech.GrahamGHS.FourColor

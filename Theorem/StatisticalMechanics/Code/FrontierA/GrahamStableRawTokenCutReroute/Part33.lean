/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute.Part32
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem exists_canonicalStableRawComponentFirstChargeOccupant_of_card_lt
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
    let first := canonicalStableRawComponentReferenceOwnerCollisionEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let incident := CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let natural := canonicalStableRawComponentNaturalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let hnatural := canonicalStableRawComponentNaturalToken_incident
      ends m j k l zero hloop hjk hkl hk0 p hno component
    ∃ state : StatMech.FrontierA.RelationPartialMatching.HoleState incident,
      ∃ collision : StatMech.FrontierA.crossCollision selfMap directMap,
      ∃ third : CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        state.hole.1 = collision.1.1.1 ∧
        (state.move natural hnatural).hole.1 = collision.1.2.1 ∧
        state.matching.toFun third = some (first collision) ∧
        third ≠ state.hole ∧
        third ≠ (state.move natural hnatural).hole ∧
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          u.target = canonicalStableRawLeftTokenTarget
              ends m j k l zero hloop hjk hkl hk0 p (first collision).1 ∧
          (CanonicalStableRawOwnerStableOutput
                ends m j k l zero hloop hjk hkl hk0 p state.hole.1 u ∨
              CanonicalStableRawOwnerAdvancingOutput
                ends m j k l zero hloop hjk hkl hk0 p state.hole.1 u) ∧
          canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
  classical
  dsimp only
  let selfMap := canonicalStableRawComponentSelfEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let directMap := canonicalStableRawComponentDirectEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let first := canonicalStableRawComponentReferenceOwnerCollisionEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let incident := CanonicalStableRawComponentIncident
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let natural := canonicalStableRawComponentNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let hnatural := canonicalStableRawComponentNaturalToken_incident
    ends m j k l zero hloop hjk hkl hk0 p hno component
  obtain ⟨state, collision, hself, hdirect⟩ :=
    exists_canonicalStableRawComponentCrossCollision_of_card_lt
      ends m j k l zero hloop hjk hkl hk0 p hno component hcard
  have hfirstIncident : incident state.hole (first collision) := by
    apply (canonicalStableRawWitnessedStateTokenIncidence_iff
      ends m j k l zero hloop hjk hkl hk0 p
        (first collision).1 state.hole.1).2
    rw [hself]
    exact canonicalStableRawReferenceOwnerLeftToken_stateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p
        collision.1.1.1 collision.1.1.2.2
  obtain ⟨third, hthird⟩ :=
    state.maximum.saturates_target_of_unmatched
      state.hole state.hole_unmatched (first collision) hfirstIncident
  have hthirdNeHole : third ≠ state.hole := by
    intro heq
    subst third
    exact state.hole_unmatched
      ((StatMech.FrontierA.RelationPartialMatching.mem_support_iff
        state.matching state.hole).2 ⟨first collision, hthird⟩)
  have hthirdNeDirect : third ≠ (state.move natural hnatural).hole := by
    intro heq
    have hfirstNatural : first collision = natural state.hole := by
      apply Option.some.inj
      exact hthird.symm.trans
        (heq ▸ state.matching_apply_move_hole natural hnatural)
    apply canonicalStableRawComponentReferenceOwnerCollisionEmbedding_ne_self
      ends m j k l zero hloop hjk hkl hk0 p hno component
        collision collision.1.1
    calc
      first collision = natural state.hole := hfirstNatural
      _ = selfMap collision.1.1 := by
        apply Subtype.ext
        change canonicalStableRawStateLeftToken
            ends m j k l zero hloop hjk hkl hk0 p hno state.hole.1 =
          canonicalStableRawStateLeftToken
            ends m j k l zero hloop hjk hkl hk0 p hno collision.1.1.1
        rw [hself]
  have hthirdIncident : incident third (first collision) :=
    state.matching.related hthird
  have hclassify :=
    canonicalStableRawWitnessedStateTokenIncidence_sharedTokenClassification
      ends m j k l zero hloop hjk hkl hk0 p hno
        (first collision).1 state.hole.1 third.1
        hfirstIncident hthirdIncident
  have houtput : ∃ u : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p,
      u.target = canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p (first collision).1 ∧
      (CanonicalStableRawOwnerStableOutput
            ends m j k l zero hloop hjk hkl hk0 p state.hole.1 u ∨
          CanonicalStableRawOwnerAdvancingOutput
            ends m j k l zero hloop hjk hkl hk0 p state.hole.1 u) ∧
      canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
    rcases hclassify with heq | hstable | hadvancing
    · exact False.elim (hthirdNeHole (Subtype.ext heq).symm)
    · exact ⟨hstable.choose, hstable.choose_spec.1,
        Or.inl hstable.choose_spec.2.1,
        hstable.choose_spec.2.2.1.trans state.hole.2⟩
    · exact ⟨hadvancing.choose, hadvancing.choose_spec.1,
        Or.inr hadvancing.choose_spec.2.1,
        hadvancing.choose_spec.2.2.1.trans state.hole.2⟩
  exact ⟨state, collision, third, hself, hdirect, hthird,
    hthirdNeHole, hthirdNeDirect, houtput⟩


theorem exists_canonicalStableRawComponentResidualCollision_of_card_lt
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
    Nonempty (StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) := by
  classical
  by_contra hnone
  have hdisjoint : ∀ collision direct,
      canonicalStableRawComponentReferenceSourceCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision ≠
        canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component direct := by
    intro collision direct heq
    exact hnone ⟨⟨(collision, direct), heq⟩⟩
  obtain ⟨embedding⟩ :=
    canonicalStableRawTokenComponent_embedding_of_sourceDirectDisjoint
      ends m j k l zero hloop hjk hkl hk0 p hno component hdisjoint
  have hle := Fintype.card_le_of_embedding embedding
  omega


theorem canonicalStableRawTokenComponent_embedding_of_cardLE
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (hcard : Fintype.card
        {s : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p //
          canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno s = component} ≤
      Fintype.card
        {token : CanonicalStableRawLeftSurplusToken
            ends m j k l zero hloop hjk hkl hk0 p //
          canonicalStableRawFullLeftTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno token = component}) :
    Nonempty
      ({s : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p //
          canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno s = component} ↪
        {token : CanonicalStableRawLeftSurplusToken
            ends m j k l zero hloop hjk hkl hk0 p //
          canonicalStableRawFullLeftTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno token = component}) :=
  Function.Embedding.nonempty_of_card_le hcard


theorem canonicalStableRawExceptionalEdgeEmbedding_of_componentCardLE
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (hcard : ∀ component : Set (CanonicalStableRawExceptionalEdge
        ends m j k l zero hloop hjk hkl hk0 p),
      Fintype.card
          {s : CanonicalStableRawExceptionalEdge
              ends m j k l zero hloop hjk hkl hk0 p //
            canonicalStableRawTokenComponent
                ends m j k l zero hloop hjk hkl hk0 p hno s = component} ≤
        Fintype.card
          {token : CanonicalStableRawLeftSurplusToken
              ends m j k l zero hloop hjk hkl hk0 p //
            canonicalStableRawFullLeftTokenComponent
                ends m j k l zero hloop hjk hkl hk0 p hno token = component}) :
    Nonempty
      (CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p ↪
        CanonicalStableRawLeftSurplusToken
          ends m j k l zero hloop hjk hkl hk0 p) := by
  classical
  exact ⟨StatMech.FrontierA.embeddingOf_taggedFiberwiseCardLE
    (canonicalStableRawTokenComponent
      ends m j k l zero hloop hjk hkl hk0 p hno)
    (canonicalStableRawFullLeftTokenComponent
      ends m j k l zero hloop hjk hkl hk0 p hno) hcard⟩


theorem canonicalStableRawCollisionTokenEmbedding_of_componentCardLE
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (hcard : ∀ component : Set (CanonicalStableRawExceptionalEdge
        ends m j k l zero hloop hjk hkl hk0 p),
      Fintype.card
          {s : CanonicalStableRawExceptionalEdge
              ends m j k l zero hloop hjk hkl hk0 p //
            canonicalStableRawTokenComponent
                ends m j k l zero hloop hjk hkl hk0 p hno s = component} ≤
        Fintype.card
          {token : CanonicalStableRawLeftSurplusToken
              ends m j k l zero hloop hjk hkl hk0 p //
            canonicalStableRawFullLeftTokenComponent
                ends m j k l zero hloop hjk hkl hk0 p hno token = component}) :
    CanonicalStableRawCollisionTokenEmbedding
      ends m j k l zero hloop hjk hkl hk0 p := by
  classical
  obtain ⟨stateEmbedding⟩ :=
    canonicalStableRawExceptionalEdgeEmbedding_of_componentCardLE
      ends m j k l zero hloop hjk hkl hk0 p hno hcard
  let stateEquiv :=
    canonicalStableRawExceptionalEdgeEquivRightCollisionToken
      ends m j k l zero hloop hjk hkl hk0 p
  exact ⟨stateEquiv.symm.toEmbedding.trans stateEmbedding⟩

end StatMech.GrahamGHS.FourColor

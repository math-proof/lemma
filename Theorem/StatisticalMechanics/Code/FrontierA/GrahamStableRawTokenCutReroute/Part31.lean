/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute.Part30
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalStableRawComponentSecondCollisionCharge_of_sourceDirectDisjoint
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (hdisjoint : ∀ collision direct,
      canonicalStableRawComponentReferenceSourceCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision ≠
        canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component direct) :
    CanonicalStableRawComponentSecondCollisionCharge
      ends m j k l zero hloop hjk hkl hk0 p hno component := by
  let sourceMap := canonicalStableRawComponentReferenceSourceCollisionEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let selfMap := canonicalStableRawComponentSelfEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let directMap := canonicalStableRawComponentDirectEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let first := canonicalStableRawComponentReferenceOwnerCollisionEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  refine ⟨sourceMap, ?_, hdisjoint, ?_⟩
  · intro collision self heq
    let selfCollision : StatMech.FrontierA.crossCollision sourceMap selfMap :=
      ⟨(collision, self), heq⟩
    let directCollision :=
      canonicalStableRawReferenceSourceSelfCollisionToDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component selfCollision
    exact hdisjoint collision directCollision.1.2 directCollision.2
  · intro collision old
    exact canonicalStableRawComponentReferenceSourceCollisionEmbedding_ne_firstRange
      ends m j k l zero hloop hjk hkl hk0 p hno component collision old


theorem canonicalStableRawComponentSecondCollisionCharge_of_cardLE
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (hcard : Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component) ≤
        Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    CanonicalStableRawComponentSecondCollisionCharge
      ends m j k l zero hloop hjk hkl hk0 p hno component := by
  classical
  let Self := CanonicalStableRawComponentSelfState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let Direct := CanonicalStableRawComponentDirectState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let State := CanonicalStableRawComponentState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let Token := CanonicalStableRawComponentToken
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let selfMap := canonicalStableRawComponentSelfEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let directMap := canonicalStableRawComponentDirectEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let first := canonicalStableRawComponentReferenceOwnerCollisionEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let join : Self ⊕ Direct ↪ State := by
    let toState : Self ⊕ Direct → State
      | Sum.inl s => ⟨s.1, s.2.1⟩
      | Sum.inr s => ⟨s.1, s.2.1⟩
    refine ⟨toState, ?_⟩
    intro x y hxy
    cases x with
    | inl x =>
        cases y with
        | inl y =>
            have hv : x.1 = y.1 :=
              congrArg (fun z : State => z.1) hxy
            exact congrArg Sum.inl (Subtype.ext hv)
        | inr y =>
            exfalso
            apply y.2.2
            rw [← congrArg Subtype.val hxy]
            exact x.2.2
    | inr x =>
        cases y with
        | inl y =>
            exfalso
            apply x.2.2
            rw [congrArg Subtype.val hxy]
            exact y.2.2
        | inr y =>
            have hv : x.1 = y.1 :=
              congrArg (fun z : State => z.1) hxy
            exact congrArg Sum.inr (Subtype.ext hv)
  have hsumCard : Fintype.card Self + Fintype.card Direct ≤
      Fintype.card Token := by
    have hjoin := Fintype.card_le_of_injective join join.injective
    simpa only [Self, Direct, State, Token, Fintype.card_sum] using
      hjoin.trans hcard
  exact StatMech.FrontierA.exists_secondCollisionCharge_of_card_le
    selfMap directMap first
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding_ne_self
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      hsumCard


theorem canonicalStableRawComponentCrossCollision_classification
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    CanonicalStableRawSelfDirectTokenCollision
      ends m j k l zero hloop hjk hkl hk0 p hno
        collision.1.1.1 collision.1.2.1 := by
  apply canonicalStableRawSelfDirectTokenCollision_of_token_eq
      ends m j k l zero hloop hjk hkl hk0 p hno
        collision.1.1.1 collision.1.2.1 collision.1.1.2.2 collision.1.2.2.2
  have htoken := congrArg Subtype.val collision.2
  simpa only [canonicalStableRawComponentSelfEmbedding_apply,
    canonicalStableRawComponentDirectEmbedding_apply] using htoken

theorem canonicalStableRawComponentCrossCollision_stable_or_advancing
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    CanonicalStableRawOwnerStableStep
        ends m j k l zero hloop hjk hkl hk0 p hno collision.1.1.1 ∨
      CanonicalStableRawOwnerAdvancingStep
        ends m j k l zero hloop hjk hkl hk0 p hno collision.1.1.1 := by
  have hclassify := canonicalStableRawComponentCrossCollision_classification
    ends m j k l zero hloop hjk hkl hk0 p hno component collision
  rcases hclassify.2.2 with ⟨_, hstable⟩ | ⟨hadvancing, _⟩
  · exact Or.inl hstable
  · exact Or.inr hadvancing


theorem canonicalStableRawComponentCrossCollision_source_injective
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    Function.Injective fun x : StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentSelfEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component) =>
      x.1.1.1.source := by
  intro x y hsource
  change x.1.1.1.source = y.1.1.1.source at hsource
  apply StatMech.FrontierA.crossCollision_fst_injective
  apply Subtype.ext
  apply canonicalStableRawExceptionalEdge_eq_of_source_target_eq hsource
  apply Subtype.ext
  calc
    x.1.1.1.target.1 = canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p x.1.1.1.source := x.1.1.2.2
    _ = canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p y.1.1.1.source := by rw [hsource]
    _ = y.1.1.1.target.1 := y.1.1.2.2.symm


theorem canonicalStableRawAdvancingCrossCollision_selfBase_eq_of_next_eq
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (x y : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hx : CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1)
    (hy : CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno y.1.1.1)
    (hnext : canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1 =
      canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno y.1.1.1) :
    canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        x.1.1.1.source =
      canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        y.1.1.1.source := by
  classical
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  let ownerX : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p x.1.1.1.target,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p x.1.1.1.target⟩
  let ownerY : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p y.1.1.1.target,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p y.1.1.1.target⟩
  have hsourceX : (next x.1.1.1).source = ownerX := by
    apply Subtype.ext
    exact hx
  have hsourceY : (next y.1.1.1).source = ownerY := by
    apply Subtype.ext
    exact hy
  have hownerXY : ownerX = ownerY := by
    calc
      ownerX = (next x.1.1.1).source := hsourceX.symm
      _ = (next y.1.1.1).source := congrArg
        (fun s : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p => s.source) hnext
      _ = ownerY := hsourceY
  have hownerSelfX : canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p ownerX = x.1.1.1.target.1 :=
    canonicalStableRawPreferredRightBase_self_eq_of_exists
      ends m j k l zero hloop hjk hkl hk0 p x.1.1.1.target
        ⟨x.1.1.1.source, x.1.1.2.2.symm⟩
  have hownerSelfY : canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p ownerY = y.1.1.1.target.1 :=
    canonicalStableRawPreferredRightBase_self_eq_of_exists
      ends m j k l zero hloop hjk hkl hk0 p y.1.1.1.target
        ⟨y.1.1.1.source, y.1.1.2.2.symm⟩
  calc
    canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        x.1.1.1.source = x.1.1.1.target.1 := x.1.1.2.2.symm
    _ = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        ownerX := hownerSelfX.symm
    _ = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        ownerY := by rw [hownerXY]
    _ = y.1.1.1.target.1 := hownerSelfY
    _ = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        y.1.1.1.source := y.1.1.2.2


theorem card_le_canonicalRawRelationNeighborhood_of_advancingCollisionBlock
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (A : Finset (StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)))
    (x₀ : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hx₀ : x₀ ∈ A)
    (hadvancing : ∀ x ∈ A, CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1)
    (hnext : ∀ x ∈ A,
      canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1 =
        canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno x₀.1.1.1) :
    ∃ sources : Finset ↑(canonicalRawCommonClosure ends m j k l zero p),
      (∀ c, c ∈ sources ↔ ∃ x ∈ A, x.1.1.1.source = c) ∧
      sources.card = A.card ∧
      A.card ≤
        (StatMech.FrontierA.finiteRelationNeighborhood
          (CanonicalRawGateRelated ends m j k l zero p)
          (sources.map ⟨Subtype.val, Subtype.val_injective⟩)).card := by
  classical
  let collisionSource := fun x : StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentSelfEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component) =>
      x.1.1.1.source
  let sources := A.image collisionSource
  have hsourceInjective : Function.Injective collisionSource := by
    intro x y hsource
    change x.1.1.1.source = y.1.1.1.source at hsource
    apply StatMech.FrontierA.crossCollision_fst_injective
    apply Subtype.ext
    apply canonicalStableRawExceptionalEdge_eq_of_source_target_eq hsource
    apply Subtype.ext
    calc
      x.1.1.1.target.1 = canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p x.1.1.1.source := x.1.1.2.2
      _ = canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p y.1.1.1.source := by rw [hsource]
      _ = y.1.1.1.target.1 := y.1.1.2.2.symm
  have hsourcesCard : sources.card = A.card := by
    exact Finset.card_image_of_injective A hsourceInjective
  have hfiber : ∀ c ∈ sources,
      canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p c =
        canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p (collisionSource x₀) := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
    exact canonicalStableRawAdvancingCrossCollision_selfBase_eq_of_next_eq
      ends m j k l zero hloop hjk hkl hk0 p hno component x x₀
        (hadvancing x hx) (hadvancing x₀ hx₀) (hnext x hx)
  refine ⟨sources, ?_, hsourcesCard, ?_⟩
  · intro c
    simp only [sources, collisionSource, Finset.mem_image]
  · rw [← hsourcesCard]
    exact card_le_canonicalRawRelationNeighborhood_of_selfBaseFiber
      ends m j k l zero hloop hjk hkl hk0 p sources
        (collisionSource x₀) hfiber


theorem exists_canonicalRawRelationNeighborhoodEmbedding_of_advancingCollisionBlock
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (A : Finset (StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)))
    (x₀ : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hx₀ : x₀ ∈ A)
    (hadvancing : ∀ x ∈ A, CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1)
    (hnext : ∀ x ∈ A,
      canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1 =
        canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno x₀.1.1.1) :
    ∃ sources : Finset ↑(canonicalRawCommonClosure ends m j k l zero p),
      (∀ c, c ∈ sources ↔ ∃ x ∈ A, x.1.1.1.source = c) ∧
      Nonempty (↑A ↪
        ↑(StatMech.FrontierA.finiteRelationNeighborhood
          (CanonicalRawGateRelated ends m j k l zero p)
          (sources.map ⟨Subtype.val, Subtype.val_injective⟩))) := by
  classical
  obtain ⟨sources, hsources, _, hcard⟩ :=
    card_le_canonicalRawRelationNeighborhood_of_advancingCollisionBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component A x₀ hx₀
        hadvancing hnext
  refine ⟨sources, hsources, ?_⟩
  apply Function.Embedding.nonempty_of_card_le
  simpa only [Fintype.card_coe] using hcard


theorem canonicalStableRawTokenComponent_embedding_of_sumEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (merged : CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component ⊕
        CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component ↪
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) :
    Nonempty (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component ↪
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  let split : CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component ->
      CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component ⊕
        CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component := fun s =>
    if hs : s.1.target.1 = canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p s.1.source then
      Sum.inl ⟨s.1, s.2, hs⟩ else Sum.inr ⟨s.1, s.2, hs⟩
  let recover :
      CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component ⊕
        CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component ->
      CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component
    | Sum.inl s => ⟨s.1, s.2.1⟩
    | Sum.inr s => ⟨s.1, s.2.1⟩
  have hrecover : Function.LeftInverse recover split := by
    intro s
    by_cases hs : s.1.target.1 = canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p s.1.source
    · simp [split, recover, hs]
    · simp [split, recover, hs]
  let splitEmbedding : CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component ↪
      CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component ⊕
        CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component :=
    ⟨split, hrecover.injective⟩
  exact ⟨splitEmbedding.trans merged⟩


theorem canonicalStableRawTokenComponent_embedding_of_secondCollisionCharge
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (hcharge : CanonicalStableRawComponentSecondCollisionCharge
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    Nonempty (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component ↪
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  let selfMap := canonicalStableRawComponentSelfEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let directMap := canonicalStableRawComponentDirectEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let first := canonicalStableRawComponentReferenceOwnerCollisionEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  obtain ⟨second, hfreshSelf, hfreshDirect, hfreshFirst⟩ := hcharge
  let merged := StatMech.FrontierA.embeddingSumOfCrossCollisionSecondCharge
    selfMap directMap first
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding_ne_self
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      second hfreshSelf hfreshDirect hfreshFirst
  exact canonicalStableRawTokenComponent_embedding_of_sumEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component merged


theorem canonicalStableRawTokenComponent_embedding_of_sourceDirectDisjoint
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (hdisjoint : ∀ collision direct,
      canonicalStableRawComponentReferenceSourceCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision ≠
        canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component direct) :
    Nonempty (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component ↪
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) :=
  canonicalStableRawTokenComponent_embedding_of_secondCollisionCharge
    ends m j k l zero hloop hjk hkl hk0 p hno component
      (canonicalStableRawComponentSecondCollisionCharge_of_sourceDirectDisjoint
        ends m j k l zero hloop hjk hkl hk0 p hno component hdisjoint)


theorem canonicalStableRawComponentSecondCollisionCharge_iff_cardLE
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    CanonicalStableRawComponentSecondCollisionCharge
        ends m j k l zero hloop hjk hkl hk0 p hno component ↔
      Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component) ≤
        Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  constructor
  · intro hcharge
    obtain ⟨embedding⟩ :=
      canonicalStableRawTokenComponent_embedding_of_secondCollisionCharge
        ends m j k l zero hloop hjk hkl hk0 p hno component hcharge
    exact Fintype.card_le_of_injective embedding embedding.injective
  · exact canonicalStableRawComponentSecondCollisionCharge_of_cardLE
      ends m j k l zero hloop hjk hkl hk0 p hno component


theorem canonicalStableRawTokenComponent_embedding_of_collisionCharge
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (hcharge : CanonicalStableRawComponentCollisionCharge
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    Nonempty (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component ↪
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  let selfMap := canonicalStableRawComponentSelfEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let directMap := canonicalStableRawComponentDirectEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  obtain ⟨charge, hfreshSelf, hfreshDirect⟩ := hcharge
  let merged := StatMech.FrontierA.embeddingSumOfCrossCollisionCharge
    selfMap directMap charge hfreshSelf hfreshDirect
  let split : CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component ->
      CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component ⊕
        CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component := fun s =>
    if hs : s.1.target.1 = canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p s.1.source then
      Sum.inl ⟨s.1, s.2, hs⟩ else Sum.inr ⟨s.1, s.2, hs⟩
  let recover :
      CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component ⊕
        CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component ->
      CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component
    | Sum.inl s => ⟨s.1, s.2.1⟩
    | Sum.inr s => ⟨s.1, s.2.1⟩
  have hrecover : Function.LeftInverse recover split := by
    intro s
    by_cases hs : s.1.target.1 = canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p s.1.source
    · simp [split, recover, hs]
    · simp [split, recover, hs]
  let splitEmbedding : CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component ↪
      CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component ⊕
        CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component :=
    ⟨split, hrecover.injective⟩
  exact ⟨splitEmbedding.trans merged⟩


end StatMech.GrahamGHS.FourColor

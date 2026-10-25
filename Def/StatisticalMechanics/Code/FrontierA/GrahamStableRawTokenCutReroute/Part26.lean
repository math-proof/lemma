/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute.Part26
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def
    canonicalStableRawReferenceSourceDirectCollisionToUnusedDirectEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentReferenceSourceCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component) ↪
      {direct : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component //
        ∀ old : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component),
          direct ≠ old.1.2} := by
  let sourceMap := canonicalStableRawComponentReferenceSourceCollisionEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let directMap := canonicalStableRawComponentDirectEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let f : StatMech.FrontierA.crossCollision sourceMap directMap ->
      {direct : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component //
        ∀ old : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          directMap, direct ≠ old.1.2} := fun collision =>
    ⟨collision.1.2, by
      intro old heq
      apply canonicalStableRawComponentReferenceSourceCollisionEmbedding_ne_firstRange
        ends m j k l zero hloop hjk hkl hk0 p hno component
          collision.1.1 old.1.1
      calc
        sourceMap collision.1.1 = directMap collision.1.2 := collision.2
        _ = directMap old.1.2 := congrArg directMap heq
        _ = canonicalStableRawComponentReferenceOwnerCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component
              old.1.1 := old.2.symm⟩
  refine ⟨f, ?_⟩
  intro x y hxy
  apply StatMech.FrontierA.crossCollision_snd_injective
  exact congrArg Subtype.val hxy


noncomputable def canonicalStableRawResidualTargetBlockSourceEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (A : Finset (StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)))
    (x₀ : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (htarget : ∀ x ∈ A, x.1.2.1.target = x₀.1.2.1.target) :
    ((↑A ⊕ ↑A) ⊕ Unit) ↪
      {source : ↑(canonicalRawCommonClosure ends m j k l zero p) //
        CanonicalRawGateRelated ends m j k l zero p source.1
          x₀.1.2.1.target.1} := by
  let unused :=
    canonicalStableRawReferenceSourceDirectCollisionToUnusedDirectEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component
  let owner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p x₀.1.2.1.target,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p x₀.1.2.1.target⟩
  let f : ((↑A ⊕ ↑A) ⊕ Unit) →
      {source : ↑(canonicalRawCommonClosure ends m j k l zero p) //
        CanonicalRawGateRelated ends m j k l zero p source.1
          x₀.1.2.1.target.1}
    | Sum.inl (Sum.inl x) =>
        ⟨x.1.1.2.1.source, by
          rw [← htarget x.1 x.2]
          exact x.1.1.2.1.related⟩
    | Sum.inl (Sum.inr x) =>
        ⟨x.1.1.1.1.2.1.source, by
          rw [← htarget x.1 x.2]
          rw [canonicalStableRawComponentReferenceSource_directCollision_target
            ends m j k l zero hloop hjk hkl hk0 p hno component x.1]
          exact x.1.1.1.1.2.1.related⟩
    | Sum.inr _ =>
        ⟨owner, canonicalStableRawPreferredRightBase_related
          ends m j k l zero hloop hjk hkl hk0 p x₀.1.2.1.target⟩
  have hexposedTarget (x : ↑A) : x.1.1.2.1.target = x₀.1.2.1.target :=
    htarget x.1 x.2
  have hrootTarget (x : ↑A) :
      x.1.1.1.1.2.1.target = x₀.1.2.1.target :=
    (canonicalStableRawComponentReferenceSource_directCollision_target
      ends m j k l zero hloop hjk hkl hk0 p hno component x.1).symm.trans
        (htarget x.1 x.2)
  have hexposedInjective : Function.Injective fun x : ↑A =>
      x.1.1.2.1.source := by
    intro x y hs
    apply Subtype.ext
    apply StatMech.FrontierA.crossCollision_snd_injective
      (canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
    apply Subtype.ext
    exact canonicalStableRawExceptionalEdge_eq_of_source_target_eq hs
      ((hexposedTarget x).trans (hexposedTarget y).symm)
  have hrootInjective : Function.Injective fun x : ↑A =>
      x.1.1.1.1.2.1.source := by
    intro x y hs
    apply Subtype.ext
    apply StatMech.FrontierA.crossCollision_fst_injective
      (canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
    apply StatMech.FrontierA.crossCollision_snd_injective
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
    apply Subtype.ext
    exact canonicalStableRawExceptionalEdge_eq_of_source_target_eq hs
      ((hrootTarget x).trans (hrootTarget y).symm)
  have hexposedRootNe (x y : ↑A) :
      x.1.1.2.1.source ≠ y.1.1.1.1.2.1.source := by
    intro hs
    apply (unused x.1).2 y.1.1.1
    apply Subtype.ext
    exact canonicalStableRawExceptionalEdge_eq_of_source_target_eq hs
      ((hexposedTarget x).trans (hrootTarget y).symm)
  have hexposedOwnerNe (x : ↑A) : x.1.1.2.1.source ≠ owner := by
    intro hs
    apply x.1.1.2.1.exceptional
    calc
      x.1.1.2.1.source.1 = owner.1 := congrArg Subtype.val hs
      _ = canonicalStableRawPreferredRightBase ends m j k l zero
          hloop hjk hkl hk0 p x₀.1.2.1.target := rfl
      _ = canonicalStableRawPreferredRightBase ends m j k l zero
          hloop hjk hkl hk0 p x.1.1.2.1.target := by rw [hexposedTarget x]
  have hrootOwnerNe (x : ↑A) : x.1.1.1.1.2.1.source ≠ owner := by
    intro hs
    apply x.1.1.1.1.2.1.exceptional
    calc
      x.1.1.1.1.2.1.source.1 = owner.1 := congrArg Subtype.val hs
      _ = canonicalStableRawPreferredRightBase ends m j k l zero
          hloop hjk hkl hk0 p x₀.1.2.1.target := rfl
      _ = canonicalStableRawPreferredRightBase ends m j k l zero
          hloop hjk hkl hk0 p x.1.1.1.1.2.1.target := by rw [hrootTarget x]
  refine ⟨f, ?_⟩
  intro x y hxy
  cases x with
  | inl x =>
      cases x with
      | inl x =>
          cases y with
          | inl y =>
              cases y with
              | inl y =>
                  congr 2
                  exact hexposedInjective (congrArg Subtype.val hxy)
              | inr y =>
                  exfalso
                  exact hexposedRootNe x y (congrArg Subtype.val hxy)
          | inr y =>
              exfalso
              exact hexposedOwnerNe x (congrArg Subtype.val hxy)
      | inr x =>
          cases y with
          | inl y =>
              cases y with
              | inl y =>
                  exfalso
                  exact hexposedRootNe y x (congrArg Subtype.val hxy).symm
              | inr y =>
                  congr 2
                  exact hrootInjective (congrArg Subtype.val hxy)
          | inr y =>
              exfalso
              exact hrootOwnerNe x (congrArg Subtype.val hxy)
  | inr x =>
      cases y with
      | inl y =>
          cases y with
          | inl y =>
              exfalso
              exact hexposedOwnerNe y (congrArg Subtype.val hxy).symm
          | inr y =>
              exfalso
              exact hrootOwnerNe y (congrArg Subtype.val hxy).symm
      | inr y => rfl


end StatMech.GrahamGHS.FourColor

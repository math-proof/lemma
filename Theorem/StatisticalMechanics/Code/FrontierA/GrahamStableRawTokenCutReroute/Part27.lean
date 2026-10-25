/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute.Part26
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalStableRawResidualTargetBlock_two_mul_card_add_one_le_degree
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
    let degree : Nat := by
      classical
      exact ((canonicalRawCommonClosure ends m j k l zero p).filter
        (fun c => CanonicalRawGateRelated ends m j k l zero p c
          x₀.1.2.1.target.1)).card
    2 * A.card + 1 ≤ degree := by
  classical
  dsimp only
  let Neighbor :=
    {source : ↑(canonicalRawCommonClosure ends m j k l zero p) //
      CanonicalRawGateRelated ends m j k l zero p source.1
        x₀.1.2.1.target.1}
  let emb := canonicalStableRawResidualTargetBlockSourceEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component A x₀ htarget
  letI : Fintype Neighbor := Fintype.ofInjective
    (fun source : Neighbor => source.1.1) (by
      intro x y hxy
      exact Subtype.ext (Subtype.ext hxy))
  have hcard := Fintype.card_le_of_injective emb emb.injective
  have hneighbor : Fintype.card Neighbor =
      ((canonicalRawCommonClosure ends m j k l zero p).filter
        (fun c => CanonicalRawGateRelated ends m j k l zero p c
          x₀.1.2.1.target.1)).card := by
    classical
    let filtered := (canonicalRawCommonClosure ends m j k l zero p).filter
      (fun c => CanonicalRawGateRelated ends m j k l zero p c
        x₀.1.2.1.target.1)
    let e : Neighbor ≃ ↑filtered := by
      refine
        { toFun := fun source =>
            ⟨source.1.1, Finset.mem_filter.mpr ⟨source.1.2, source.2⟩⟩
          invFun := fun source =>
            ⟨⟨source.1, (Finset.mem_filter.mp source.2).1⟩,
              (Finset.mem_filter.mp source.2).2⟩
          left_inv := ?_
          right_inv := ?_ }
      · intro source
        apply Subtype.ext
        apply Subtype.ext
        rfl
      · intro source
        apply Subtype.ext
        rfl
    calc
      Fintype.card Neighbor = Fintype.card ↑filtered := Fintype.card_congr e
      _ = filtered.card := Fintype.card_coe filtered
      _ = _ := rfl
  rw [Fintype.card_sum, Fintype.card_sum] at hcard
  rw [Fintype.card_coe A] at hcard
  change A.card + A.card + Fintype.card Unit ≤ Fintype.card Neighbor at hcard
  rw [Fintype.card_unique, hneighbor] at hcard
  omega


theorem card_le_canonicalRawRelationNeighborhood_of_residualTargetFiberBlock
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
    (htarget : ∀ x ∈ A, x.1.2.1.target = x₀.1.2.1.target)
    (r : ↑(canonicalRawCommonClosure ends m j k l zero p))
    (hbase : ∀ x ∈ A,
      canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        x.1.2.1.source =
      canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p r) :
    ∃ sources : Finset ↑(canonicalRawCommonClosure ends m j k l zero p),
      sources.card = 2 * A.card ∧
        sources.card ≤
          (StatMech.FrontierA.finiteRelationNeighborhood
            (CanonicalRawGateRelated ends m j k l zero p)
            (sources.map ⟨Subtype.val, Subtype.val_injective⟩)).card := by
  classical
  let block := canonicalStableRawResidualTargetBlockSourceEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component A x₀ htarget
  let sourceEmbedding : (↑A ⊕ ↑A) ↪
      ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨fun x => (block (Sum.inl x)).1, fun x y hxy => by
      apply Sum.inl_injective
      apply block.injective
      apply Subtype.ext
      exact hxy⟩
  let sources := Finset.univ.image sourceEmbedding
  have hsourcesCard : sources.card = 2 * A.card := by
    change (Finset.univ.image sourceEmbedding).card = 2 * A.card
    rw [Finset.card_image_of_injective _ sourceEmbedding.injective,
      Finset.card_univ, Fintype.card_sum]
    rw [Fintype.card_coe A]
    omega
  have hfiber : ∀ c ∈ sources,
      canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p c =
        canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p r := by
    intro c hc
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hc
    cases x with
    | inl x => exact hbase x.1 x.2
    | inr x =>
        exact (canonicalStableRawComponentReferenceSource_directCollision_selfBase_eq
          ends m j k l zero hloop hjk hkl hk0 p hno component x.1).symm.trans
            (hbase x.1 x.2)
  refine ⟨sources, hsourcesCard, ?_⟩
  exact card_le_canonicalRawRelationNeighborhood_of_selfBaseFiber
    ends m j k l zero hloop hjk hkl hk0 p sources r hfiber


theorem canonicalStableRaw_referenceSourceDirectCollision_card_add_le_direct
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    Nat.card (StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)) +
      Nat.card (StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentReferenceSourceCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)) ≤
      Nat.card (CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  let first := canonicalStableRawComponentReferenceOwnerCollisionEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let sourceMap := canonicalStableRawComponentReferenceSourceCollisionEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let directMap := canonicalStableRawComponentDirectEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let unused :=
    canonicalStableRawReferenceSourceDirectCollisionToUnusedDirectEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component
  let combined : StatMech.FrontierA.crossCollision first directMap ⊕
        StatMech.FrontierA.crossCollision sourceMap directMap →
      CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component
    | Sum.inl old => old.1.2
    | Sum.inr collision => (unused collision).1
  have hinjective : Function.Injective combined := by
    intro x y hxy
    cases x with
    | inl x =>
        cases y with
        | inl y =>
            congr 1
            exact StatMech.FrontierA.crossCollision_snd_injective
              first directMap hxy
        | inr y =>
            exfalso
            exact (unused y).2 x hxy.symm
    | inr x =>
        cases y with
        | inl y =>
            exfalso
            exact (unused x).2 y hxy
        | inr y =>
            congr 1
            apply unused.injective
            apply Subtype.ext
            exact hxy
  letI : Fintype (CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :=
    Fintype.ofFinite _
  letI : Fintype (CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :=
    Fintype.ofFinite _
  letI : DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) :=
    Classical.decEq _
  letI : Fintype (StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      directMap) := Fintype.ofInjective
    (fun collision => collision.1.1)
    (StatMech.FrontierA.crossCollision_fst_injective
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component) directMap)
  letI : Fintype (StatMech.FrontierA.crossCollision first directMap) :=
    Fintype.ofInjective (fun collision => collision.1.1)
      (StatMech.FrontierA.crossCollision_fst_injective first directMap)
  letI : Fintype (StatMech.FrontierA.crossCollision sourceMap directMap) :=
    Fintype.ofInjective (fun collision => collision.1.1)
      (StatMech.FrontierA.crossCollision_fst_injective sourceMap directMap)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_sum] using
    Fintype.card_le_of_injective combined hinjective


end StatMech.GrahamGHS.FourColor

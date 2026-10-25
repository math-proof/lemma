/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute.Part24
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


@[simp] theorem canonicalStableRawComponentReferenceSourceCollisionEmbedding_apply
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (x : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    (canonicalStableRawComponentReferenceSourceCollisionEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component x).1 =
      canonicalStableRawReferenceSourceLeftToken
        ends m j k l zero hloop hjk hkl hk0 p
          x.1.1.1.1.1 x.1.1.1.1.2.2 := rfl

theorem canonicalStableRawComponentReferenceSourceCollisionEmbedding_ne_first
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (x : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component x ≠
      canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component x.1.1 := by
  intro h
  apply canonicalStableRawReferenceOwner_source_ne
    ends m j k l zero hloop hjk hkl hk0 p x.1.1.1.1.1
  have hsource := congrArg
    (fun token : CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component => token.1.1) h
  simpa only [canonicalStableRawComponentReferenceSourceCollisionEmbedding_apply,
    canonicalStableRawComponentReferenceOwnerCollisionEmbedding_apply,
    canonicalStableRawReferenceSourceLeftToken_source,
    canonicalStableRawReferenceOwnerLeftToken_source] using hsource


theorem canonicalStableRawComponentReferenceSourceCollisionEmbedding_ne_firstRange
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (x : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (old : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component x ≠
      canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component old := by
  intro heq
  let sx := x.1.1.1.1.1
  let sy := old.1.1.1
  let c := sx.source
  let r := canonicalStableRawReferenceOwner
    ends m j k l zero hloop hjk hkl hk0 p sx
  let d := sy.source
  let q := canonicalStableRawReferenceOwner
    ends m j k l zero hloop hjk hkl hk0 p sy
  have hcr : c ≠ r := canonicalStableRawReferenceOwner_source_ne
    ends m j k l zero hloop hjk hkl hk0 p sx
  have hdq : d ≠ q := canonicalStableRawReferenceOwner_source_ne
    ends m j k l zero hloop hjk hkl hk0 p sy
  have hbaseCR : canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p c =
      canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p r :=
    canonicalStableRawReferenceOwner_sourceBase
      ends m j k l zero hloop hjk hkl hk0 p sx x.1.1.1.1.2.2
  have hbaseDQ : canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p d =
      canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p q :=
    canonicalStableRawReferenceOwner_sourceBase
      ends m j k l zero hloop hjk hkl hk0 p sy old.1.1.2.2
  have hcq : c = q := by
    have h := congrArg
      (fun token : CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component => token.1.1) heq
    simpa only [canonicalStableRawComponentReferenceSourceCollisionEmbedding_apply,
      canonicalStableRawComponentReferenceOwnerCollisionEmbedding_apply,
      canonicalStableRawReferenceSourceLeftToken_source,
      canonicalStableRawReferenceOwnerLeftToken_source] using h
  have htarget : (canonicalStableRawReferenceAlternateData
        ends m j k l zero hloop hjk hkl hk0 p c r hcr hbaseCR).target =
      (canonicalStableRawReferenceAlternateData
        ends m j k l zero hloop hjk hkl hk0 p d q hdq hbaseDQ).target := by
    have h := congrArg
      (fun token : CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component => token.1.2.1) heq
    exact h
  have hcomm := canonicalStableRawReferenceAlternateData_target_comm
    ends m j k l zero hloop hjk hkl hk0 p c r hcr hbaseCR
  have hrd : r = d :=
    canonicalStableRawReferenceAlternateData_target_injective_of_reference_eq
      ends m j k l zero hloop hjk hkl hk0 p r d c q hcr.symm hdq
        hbaseCR.symm hbaseDQ hcq (hcomm.symm.trans htarget)
  have htargetState : sy.target = sx.target := by
    apply Subtype.ext
    calc
      sy.target.1 = canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p d := old.1.1.2.2
      _ = canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p r := by rw [← hrd]
      _ = sx.target.1 := canonicalStableRawReferenceOwner_selfBase
        ends m j k l zero hloop hjk hkl hk0 p sx x.1.1.1.1.2.2
  apply sy.exceptional
  calc
    sy.source.1 = d.1 := rfl
    _ = r.1 := congrArg Subtype.val hrd.symm
    _ = canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p sx.target := rfl
    _ = canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p sy.target := by rw [htargetState]

theorem canonicalStableRawComponentReferenceSourceCollisionEmbedding_ne_occupant
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (x : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component x ≠
      canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component x.1.2 := by
  intro h
  apply x.1.1.1.1.1.exceptional
  have htoken : canonicalStableRawReferenceSourceLeftToken
        ends m j k l zero hloop hjk hkl hk0 p
          x.1.1.1.1.1 x.1.1.1.1.2.2 =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno x.1.2.1 := by
    simpa only [canonicalStableRawComponentReferenceSourceCollisionEmbedding_apply,
      canonicalStableRawComponentDirectEmbedding_apply] using
        congrArg Subtype.val h
  have hsource : x.1.1.1.1.1.source =
      (canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno x.1.2.1).1 := by
    simpa only [canonicalStableRawReferenceSourceLeftToken_source] using
      congrArg Sigma.fst htoken
  unfold canonicalStableRawStateLeftToken at hsource
  rw [dif_neg x.1.2.2.2] at hsource
  calc
    x.1.1.1.1.1.source.1 = x.1.2.1.source.1 := congrArg Subtype.val hsource
    _ = canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p x.1.1.1.1.1.target :=
      canonicalStableRawComponentReferenceOwner_directOccupant_source
        ends m j k l zero hloop hjk hkl hk0 p hno component x


theorem canonicalStableRawComponentReferenceSource_selfCollision_forces_advancing
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (x : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (self : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hcollision : canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component x =
      canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component self) :
    self.1 = x.1.1.1.1.1 ∧
      CanonicalStableRawOwnerAdvancingStep
        ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1.1.1 ∧
      x.1.2.1 = canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1.1.1 := by
  let s := x.1.1.1.1.1
  let d := x.1.2.1
  have htoken : canonicalStableRawReferenceSourceLeftToken
        ends m j k l zero hloop hjk hkl hk0 p s x.1.1.1.1.2.2 =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno self.1 := by
    simpa only [canonicalStableRawComponentReferenceSourceCollisionEmbedding_apply,
      canonicalStableRawComponentSelfEmbedding_apply] using
        congrArg Subtype.val hcollision
  have hsource : s.source = self.1.source := by
    have h := congrArg Sigma.fst htoken
    unfold canonicalStableRawStateLeftToken at h
    rw [dif_pos self.2.2] at h
    exact h
  have hstate : self.1 = s := by
    apply canonicalStableRawExceptionalEdge_eq_of_source_target_eq hsource.symm
    apply Subtype.ext
    calc
      self.1.target.1 = canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p self.1.source := self.2.2
      _ = canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p s.source := by rw [hsource]
      _ = s.target.1 := x.1.1.1.1.2.2.symm
  have hsourceReroute : canonicalStableRawReferenceSourceLeftToken
        ends m j k l zero hloop hjk hkl hk0 p s x.1.1.1.1.2.2 =
      canonicalStableRawSelfRerouteLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s x.1.1.1.1.2.2 := by
    calc
      canonicalStableRawReferenceSourceLeftToken
          ends m j k l zero hloop hjk hkl hk0 p s x.1.1.1.1.2.2 =
        canonicalStableRawStateLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno self.1 := htoken
      _ = canonicalStableRawStateLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno s :=
        congrArg (canonicalStableRawStateLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno) hstate
      _ = canonicalStableRawSelfRerouteLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno s x.1.1.1.1.2.2 := by
        unfold canonicalStableRawStateLeftToken
        rw [dif_pos x.1.1.1.1.2.2]
  have hownerReroute :=
    canonicalStableRawReferenceOwnerLeftToken_eq_selfOwnerReroute
      ends m j k l zero hloop hjk hkl hk0 p hno s
        x.1.1.1.1.2.2 hsourceReroute
  have hownerDirect : canonicalStableRawSelfOwnerRerouteLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s x.1.1.1.1.2.2 =
      canonicalStableRawDirectLeftToken
        ends m j k l zero hloop hjk hkl hk0 p d x.1.2.2.2 := by
    have hfirst : canonicalStableRawReferenceOwnerLeftToken
          ends m j k l zero hloop hjk hkl hk0 p s x.1.1.1.1.2.2 =
        canonicalStableRawStateLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno d := by
      simpa only [canonicalStableRawComponentReferenceOwnerCollisionEmbedding_apply,
        canonicalStableRawComponentDirectEmbedding_apply] using
          congrArg Subtype.val x.2
    unfold canonicalStableRawStateLeftToken at hfirst
    rw [dif_neg x.1.2.2.2] at hfirst
    exact hownerReroute.symm.trans hfirst
  have hadvancing : CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno s := by
    rcases canonicalStableRawExceptionalEdgeNext_advancing_or_ownerStable
        ends m j k l zero hloop hjk hkl hk0 p hno s with
      hadvancing | hstable
    · exact hadvancing
    · exfalso
      apply canonicalStableRawSelfOwnerReroute_not_exceptional_of_ownerStable
        ends m j k l zero hloop hjk hkl hk0 p hno s
          x.1.1.1.1.2.2 hstable
      rw [hownerDirect]
      exact canonicalStableRawDirectLeftToken_isExceptional
        ends m j k l zero hloop hjk hkl hk0 p d x.1.2.2.2
  have hnextSource : (canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno s).source =
      canonicalStableRawReferenceOwner
        ends m j k l zero hloop hjk hkl hk0 p s := by
    apply Subtype.ext
    exact hadvancing
  have hdSource : d.source = canonicalStableRawReferenceOwner
      ends m j k l zero hloop hjk hkl hk0 p s := by
    have h := congrArg Sigma.fst hownerDirect
    exact h.symm
  have hdTarget : d.target = (canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno s).target := by
    apply Subtype.ext
    exact (congrArg (fun token : CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p => token.2.1) hownerDirect).symm
  refine ⟨hstate, hadvancing, ?_⟩
  apply canonicalStableRawExceptionalEdge_eq_of_source_target_eq
  · exact hdSource.trans hnextSource.symm
  · exact hdTarget


theorem canonicalStableRawComponentReferenceSource_selfCollision_next_injective
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    Function.Injective fun collision : StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentReferenceSourceCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentSelfEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component) =>
      canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno
          collision.1.1.1.1.1.1.1 := by
  intro x y hnext
  have hx :=
    canonicalStableRawComponentReferenceSource_selfCollision_forces_advancing
      ends m j k l zero hloop hjk hkl hk0 p hno component
        x.1.1 x.1.2 x.2
  have hy :=
    canonicalStableRawComponentReferenceSource_selfCollision_forces_advancing
      ends m j k l zero hloop hjk hkl hk0 p hno component
        y.1.1 y.1.2 y.2
  apply StatMech.FrontierA.crossCollision_fst_injective
  apply StatMech.FrontierA.crossCollision_snd_injective
  apply Subtype.ext
  exact hx.2.2.trans (hnext.trans hy.2.2.symm)


end StatMech.GrahamGHS.FourColor

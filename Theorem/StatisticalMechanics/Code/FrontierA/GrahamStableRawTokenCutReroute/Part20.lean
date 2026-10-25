/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute.Part19
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


@[simp] theorem canonicalStableRawReferenceOwnerLeftToken_source
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    (canonicalStableRawReferenceOwnerLeftToken
      ends m j k l zero hloop hjk hkl hk0 p s hself).1 =
      canonicalStableRawReferenceOwner
        ends m j k l zero hloop hjk hkl hk0 p s := rfl

@[simp] theorem canonicalStableRawReferenceOwnerLeftToken_target
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    (canonicalStableRawReferenceOwnerLeftToken
      ends m j k l zero hloop hjk hkl hk0 p s hself).2.1 =
      (canonicalStableRawReferenceOwnerAlternateData
        ends m j k l zero hloop hjk hkl hk0 p s hself).target := rfl


theorem canonicalStableRawReferenceOwnerLeftToken_stateTokenIncidence
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    CanonicalStableRawStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawReferenceOwnerLeftToken
          ends m j k l zero hloop hjk hkl hk0 p s hself) s := by
  classical
  let owner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p s.target,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p s.target⟩
  have hsourceOwner : s.source ≠ owner := by
    intro h
    apply s.exceptional
    exact congrArg Subtype.val h
  have hownerSelf : canonicalStableRawSelfBase ends m j k l zero
      hloop hjk hkl hk0 p owner = s.target.1 :=
    canonicalStableRawPreferredRightBase_self_eq_of_exists
      ends m j k l zero hloop hjk hkl hk0 p s.target
        ⟨s.source, hself.symm⟩
  have hbase : canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p s.source =
      canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p owner := hself.symm.trans hownerSelf.symm
  let data := canonicalStableRawReferenceAlternateData
    ends m j k l zero hloop hjk hkl hk0 p s.source owner
      hsourceOwner hbase
  change (owner = s.source ∨ owner = owner) ∧
    CanonicalRawGateRelated ends m j k l zero p s.source.1 data.target ∧
    CanonicalRawGateRelated ends m j k l zero p owner.1 data.target
  exact ⟨Or.inr rfl, data.sourceRelated, data.referenceRelated⟩

theorem canonicalStableRawReferenceOwnerLeftToken_fullComponent
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    canonicalStableRawFullLeftTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno
          (canonicalStableRawReferenceOwnerLeftToken
            ends m j k l zero hloop hjk hkl hk0 p s hself) =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s := by
  exact canonicalStableRawLeftToken_fullComponent_of_stateTokenIncidence
    ends m j k l zero hloop hjk hkl hk0 p hno _ s
      (canonicalStableRawReferenceOwnerLeftToken_stateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p s hself)

set_option maxHeartbeats 800000 in

lemma canonicalStableRawReferenceOwnerLeftToken_eq_imp
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (s t : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hselfS : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source)
    (hselfT : t.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p t.source)
    (htoken : canonicalStableRawReferenceOwnerLeftToken
        ends m j k l zero hloop hjk hkl hk0 p s hselfS =
      canonicalStableRawReferenceOwnerLeftToken
        ends m j k l zero hloop hjk hkl hk0 p t hselfT) :
    s = t := by
  classical
  let ownerS : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    canonicalStableRawReferenceOwner
      ends m j k l zero hloop hjk hkl hk0 p s
  let ownerT : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    canonicalStableRawReferenceOwner
      ends m j k l zero hloop hjk hkl hk0 p t
  have howner : ownerS = ownerT := by
    have hsource := congrArg Sigma.fst htoken
    simpa only [canonicalStableRawReferenceOwnerLeftToken_source] using hsource
  have hownerSelfS : canonicalStableRawSelfBase ends m j k l zero
      hloop hjk hkl hk0 p ownerS = s.target.1 :=
    canonicalStableRawReferenceOwner_selfBase
      ends m j k l zero hloop hjk hkl hk0 p s hselfS
  have hownerSelfT : canonicalStableRawSelfBase ends m j k l zero
      hloop hjk hkl hk0 p ownerT = t.target.1 :=
    canonicalStableRawReferenceOwner_selfBase
      ends m j k l zero hloop hjk hkl hk0 p t hselfT
  have htarget : s.target = t.target := by
    apply Subtype.ext
    calc
      s.target.1 = canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p ownerS := hownerSelfS.symm
      _ = canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p ownerT := by rw [howner]
      _ = t.target.1 := hownerSelfT
  have hsne : s.source ≠ ownerS := by
    exact canonicalStableRawReferenceOwner_source_ne
      ends m j k l zero hloop hjk hkl hk0 p s
  have htne : t.source ≠ ownerS := by
    intro h
    exact (canonicalStableRawReferenceOwner_source_ne
      ends m j k l zero hloop hjk hkl hk0 p t) (h.trans howner)
  have hbaseS : canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p s.source =
      canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p ownerS :=
    canonicalStableRawReferenceOwner_sourceBase
      ends m j k l zero hloop hjk hkl hk0 p s hselfS
  have hbaseT : canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p t.source =
      canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p ownerS :=
    (canonicalStableRawReferenceOwner_sourceBase
      ends m j k l zero hloop hjk hkl hk0 p t hselfT).trans
        (congrArg (canonicalStableRawSelfBase
          ends m j k l zero hloop hjk hkl hk0 p) howner.symm)
  have htokenTarget := congrArg (fun token :
      CanonicalStableRawLeftSurplusToken
        ends m j k l zero hloop hjk hkl hk0 p => token.2.1) htoken
  change (canonicalStableRawReferenceOwnerAlternateData
      ends m j k l zero hloop hjk hkl hk0 p s hselfS).target =
    (canonicalStableRawReferenceOwnerAlternateData
      ends m j k l zero hloop hjk hkl hk0 p t hselfT).target at htokenTarget
  unfold canonicalStableRawReferenceOwnerAlternateData at htokenTarget
  have hsources : s.source = t.source :=
    canonicalStableRawReferenceAlternateData_target_injective_of_reference_eq
      ends m j k l zero hloop hjk hkl hk0 p s.source t.source ownerS ownerT
        hsne
        (canonicalStableRawReferenceOwner_source_ne
          ends m j k l zero hloop hjk hkl hk0 p t)
        hbaseS
        (canonicalStableRawReferenceOwner_sourceBase
          ends m j k l zero hloop hjk hkl hk0 p t hselfT)
        howner htokenTarget
  exact canonicalStableRawExceptionalEdge_eq_of_source_target_eq
    hsources htarget


end StatMech.GrahamGHS.FourColor

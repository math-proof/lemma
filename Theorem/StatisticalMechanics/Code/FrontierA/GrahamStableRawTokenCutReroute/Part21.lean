/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute.Part20
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


@[simp] theorem canonicalStableRawReferenceSourceLeftToken_source
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    (canonicalStableRawReferenceSourceLeftToken
      ends m j k l zero hloop hjk hkl hk0 p s hself).1 = s.source := rfl

@[simp] theorem canonicalStableRawReferenceSourceLeftToken_target
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    (canonicalStableRawReferenceSourceLeftToken
      ends m j k l zero hloop hjk hkl hk0 p s hself).2.1 =
      (canonicalStableRawReferenceOwnerAlternateData
        ends m j k l zero hloop hjk hkl hk0 p s hself).target := rfl

theorem canonicalStableRawReferenceSourceLeftToken_stateTokenIncidence
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
        (canonicalStableRawReferenceSourceLeftToken
          ends m j k l zero hloop hjk hkl hk0 p s hself) s := by
  classical
  let data := canonicalStableRawReferenceOwnerAlternateData
    ends m j k l zero hloop hjk hkl hk0 p s hself
  change (s.source = s.source ∨
      s.source = canonicalStableRawReferenceOwner
        ends m j k l zero hloop hjk hkl hk0 p s) ∧
    CanonicalRawGateRelated ends m j k l zero p s.source.1 data.target ∧
    CanonicalRawGateRelated ends m j k l zero p
      (canonicalStableRawReferenceOwner
        ends m j k l zero hloop hjk hkl hk0 p s).1 data.target
  exact ⟨Or.inl rfl, data.sourceRelated, data.referenceRelated⟩

theorem canonicalStableRawReferenceSourceLeftToken_fullComponent
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
          (canonicalStableRawReferenceSourceLeftToken
            ends m j k l zero hloop hjk hkl hk0 p s hself) =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s :=
  canonicalStableRawLeftToken_fullComponent_of_stateTokenIncidence
    ends m j k l zero hloop hjk hkl hk0 p hno _ s
      (canonicalStableRawReferenceSourceLeftToken_stateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p s hself)


theorem canonicalStableRawReferenceSourceLeftToken_eq_imp
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
    (htoken : canonicalStableRawReferenceSourceLeftToken
        ends m j k l zero hloop hjk hkl hk0 p s hselfS =
      canonicalStableRawReferenceSourceLeftToken
        ends m j k l zero hloop hjk hkl hk0 p t hselfT) :
    s = t := by
  have hsource : s.source = t.source := by
    simpa only [canonicalStableRawReferenceSourceLeftToken_source] using
      congrArg Sigma.fst htoken
  apply canonicalStableRawExceptionalEdge_eq_of_source_target_eq hsource
  apply Subtype.ext
  calc
    s.target.1 = canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p s.source := hselfS
    _ = canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p t.source := by rw [hsource]
    _ = t.target.1 := hselfT.symm


theorem canonicalStableRawReferenceOwnerLeftToken_eq_selfOwnerReroute
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source)
    (hsource : canonicalStableRawReferenceSourceLeftToken
        ends m j k l zero hloop hjk hkl hk0 p s hself =
      canonicalStableRawSelfRerouteLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s hself) :
    canonicalStableRawReferenceOwnerLeftToken
        ends m j k l zero hloop hjk hkl hk0 p s hself =
      canonicalStableRawSelfOwnerRerouteLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s hself := by
  have htarget : (canonicalStableRawReferenceOwnerAlternateData
        ends m j k l zero hloop hjk hkl hk0 p s hself).target =
      (canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno s).target.1 := by
    have h := congrArg (fun token : CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p => token.2.1) hsource
    exact h
  have hfirst : (canonicalStableRawReferenceOwnerLeftToken
        ends m j k l zero hloop hjk hkl hk0 p s hself).1 =
      (canonicalStableRawSelfOwnerRerouteLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s hself).1 := by
    apply Subtype.ext
    rfl
  apply Sigma.ext hfirst
  cases hfirst
  apply heq_of_eq
  apply Subtype.ext
  exact htarget


end StatMech.GrahamGHS.FourColor

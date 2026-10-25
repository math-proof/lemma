/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
import Abbrev.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute.Part2
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def canonicalStableRawComponentSelfEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component ↪
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component := by
  classical
  let f : CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component ->
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component := fun s =>
    ⟨canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s.1,
      (canonicalStableRawStateLeftToken_fullComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s.1).trans s.2.1⟩
  refine ⟨f, ?_⟩
  intro s t hst
  have htokens := congrArg Subtype.val hst
  change canonicalStableRawStateLeftToken
      ends m j k l zero hloop hjk hkl hk0 p hno s.1 =
    canonicalStableRawStateLeftToken
      ends m j k l zero hloop hjk hkl hk0 p hno t.1 at htokens
  unfold canonicalStableRawStateLeftToken at htokens
  rw [dif_pos s.2.2, dif_pos t.2.2] at htokens
  apply Subtype.ext
  exact canonicalStableRawSelfReroutePredecessor_unique
    ends m j k l zero hloop hjk hkl hk0 p hno
      (canonicalStableRawSelfRerouteLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s.1 s.2.2)
      s.1 t.1 ⟨s.2.2, rfl⟩ ⟨t.2.2, htokens.symm⟩

noncomputable def canonicalStableRawComponentDirectEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component ↪
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component := by
  classical
  let f : CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component ->
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component := fun s =>
    ⟨canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s.1,
      (canonicalStableRawStateLeftToken_fullComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s.1).trans s.2.1⟩
  refine ⟨f, ?_⟩
  intro s t hst
  have htokens := congrArg Subtype.val hst
  change canonicalStableRawStateLeftToken
      ends m j k l zero hloop hjk hkl hk0 p hno s.1 =
    canonicalStableRawStateLeftToken
      ends m j k l zero hloop hjk hkl hk0 p hno t.1 at htokens
  unfold canonicalStableRawStateLeftToken at htokens
  rw [dif_neg s.2.2, dif_neg t.2.2] at htokens
  let sDirect : {u : CanonicalStableRawExceptionalEdge
        ends m j k l zero hloop hjk hkl hk0 p //
      u.target.1 ≠ canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p u.source} := ⟨s.1, s.2.2⟩
  let tDirect : {u : CanonicalStableRawExceptionalEdge
        ends m j k l zero hloop hjk hkl hk0 p //
      u.target.1 ≠ canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p u.source} := ⟨t.1, t.2.2⟩
  have htokens' : canonicalStableRawDirectLeftToken
        ends m j k l zero hloop hjk hkl hk0 p sDirect.1 sDirect.2 =
      canonicalStableRawDirectLeftToken
        ends m j k l zero hloop hjk hkl hk0 p tDirect.1 tDirect.2 := htokens
  have hsub := canonicalStableRawDirectLeftToken_injective
      ends m j k l zero hloop hjk hkl hk0 p htokens'
  apply Subtype.ext
  simpa only [sDirect, tDirect] using congrArg Subtype.val hsub

end StatMech.GrahamGHS.FourColor

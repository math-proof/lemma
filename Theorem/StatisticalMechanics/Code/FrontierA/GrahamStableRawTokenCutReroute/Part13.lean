/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute.Part12
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalStableRawSelfReroutePredecessor_unique
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (token : CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p)
    (s t : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hs : CanonicalStableRawSelfReroutePredecessor
      ends m j k l zero hloop hjk hkl hk0 p hno token s)
    (ht : CanonicalStableRawSelfReroutePredecessor
      ends m j k l zero hloop hjk hkl hk0 p hno token t) :
    s = t := by
  classical
  obtain ⟨hselfS, hsToken⟩ := hs
  obtain ⟨hselfT, htToken⟩ := ht
  have htokens := hsToken.trans htToken.symm
  have hsource : s.source = t.source := by
    exact congrArg Sigma.fst htokens
  apply canonicalStableRawExceptionalEdge_eq_of_source_target_eq hsource
  apply Subtype.ext
  calc
    s.target.1 = canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p s.source := hselfS
    _ = canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p t.source := by rw [hsource]
    _ = t.target.1 := hselfT.symm


end StatMech.GrahamGHS.FourColor

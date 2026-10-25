/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute.Part8
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def canonicalStableRawSelfRerouteLeftToken
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
    CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p := by
  classical
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  have hrelated : CanonicalRawGateRelated ends m j k l zero p
      s.source.1 (next s).target.1 :=
    (canonicalStableRawExceptionalEdgeNext_square
      ends m j k l zero hloop hjk hkl hk0 p hno s).1
  have hne : (next s).target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source := by
    intro heq
    apply canonicalStableRawExceptionalEdgeNext_target_ne
      ends m j k l zero hloop hjk hkl hk0 p hno s
    exact heq.trans hself.symm
  exact ⟨s.source, ⟨(next s).target.1, Finset.mem_erase.mpr
    ⟨hne, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrelated⟩⟩⟩⟩


noncomputable def canonicalStableRawSelfOwnerRerouteLeftToken
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
    CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p := by
  classical
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  let owner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p s.target,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p s.target⟩
  have hownerSelf : canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p owner = s.target.1 :=
    canonicalStableRawPreferredRightBase_self_eq_of_exists
      ends m j k l zero hloop hjk hkl hk0 p s.target ⟨s.source, hself.symm⟩
  have hrelated : CanonicalRawGateRelated ends m j k l zero p
      owner.1 (next s).target.1 :=
    (canonicalStableRawExceptionalEdgeNext_square
      ends m j k l zero hloop hjk hkl hk0 p hno s).2.1
  have hne : (next s).target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p owner := by
    intro heq
    apply canonicalStableRawExceptionalEdgeNext_target_ne
      ends m j k l zero hloop hjk hkl hk0 p hno s
    exact heq.trans hownerSelf
  exact ⟨owner, ⟨(next s).target.1, Finset.mem_erase.mpr
    ⟨hne, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrelated⟩⟩⟩⟩


end StatMech.GrahamGHS.FourColor

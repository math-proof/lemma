/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute.Part19
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def canonicalStableRawReferenceOwnerAlternateData
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    CanonicalStableRawReferenceAlternateData
      ends m j k l zero hloop hjk hkl hk0 p s.source
        (canonicalStableRawReferenceOwner
          ends m j k l zero hloop hjk hkl hk0 p s) :=
  canonicalStableRawReferenceAlternateData
    ends m j k l zero hloop hjk hkl hk0 p s.source
      (canonicalStableRawReferenceOwner
        ends m j k l zero hloop hjk hkl hk0 p s)
      (canonicalStableRawReferenceOwner_source_ne
        ends m j k l zero hloop hjk hkl hk0 p s)
      (canonicalStableRawReferenceOwner_sourceBase
        ends m j k l zero hloop hjk hkl hk0 p s hself)


noncomputable def canonicalStableRawReferenceOwnerLeftToken
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p := by
  classical
  let owner := canonicalStableRawReferenceOwner
    ends m j k l zero hloop hjk hkl hk0 p s
  let data := canonicalStableRawReferenceOwnerAlternateData
    ends m j k l zero hloop hjk hkl hk0 p s hself
  exact ⟨owner, ⟨data.target, Finset.mem_erase.mpr
    ⟨data.target_ne_referenceSelf,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, data.referenceRelated⟩⟩⟩⟩

end StatMech.GrahamGHS.FourColor

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute.Part18
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalStableRawReferenceOwner_source_ne
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) :
    s.source ≠ canonicalStableRawReferenceOwner
      ends m j k l zero hloop hjk hkl hk0 p s := by
  intro h
  apply s.exceptional
  exact congrArg Subtype.val h

theorem canonicalStableRawReferenceOwner_selfBase
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawReferenceOwner
          ends m j k l zero hloop hjk hkl hk0 p s) =
      s.target.1 :=
  canonicalStableRawPreferredRightBase_self_eq_of_exists
    ends m j k l zero hloop hjk hkl hk0 p s.target
      ⟨s.source, hself.symm⟩

theorem canonicalStableRawReferenceOwner_sourceBase
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source =
      canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawReferenceOwner
          ends m j k l zero hloop hjk hkl hk0 p s) :=
  hself.symm.trans
    (canonicalStableRawReferenceOwner_selfBase
      ends m j k l zero hloop hjk hkl hk0 p s hself).symm

end StatMech.GrahamGHS.FourColor

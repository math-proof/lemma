/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute.Part10
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


def CanonicalStableRawOwnerStableOutput
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (s t : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) : Prop :=
  t.source = s.source ∧
    canonicalStableRawPreferredRightBase
        ends m j k l zero hloop hjk hkl hk0 p t.target =
      canonicalStableRawPreferredRightBase
        ends m j k l zero hloop hjk hkl hk0 p s.target


def CanonicalStableRawOwnerAdvancingOutput
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (s t : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) : Prop :=
  t.source.1 = canonicalStableRawPreferredRightBase
    ends m j k l zero hloop hjk hkl hk0 p s.target


def canonicalStableRawTokenComponent
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) :
    Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) :=
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  {t | Relation.EqvGen
    (fun a b => next a = b ∨ a.target = b.target ∨
      ∃ token : CanonicalStableRawLeftSurplusToken
          ends m j k l zero hloop hjk hkl hk0 p,
        CanonicalStableRawStateTokenIncidence
            ends m j k l zero hloop hjk hkl hk0 p token a ∧
          CanonicalStableRawStateTokenIncidence
            ends m j k l zero hloop hjk hkl hk0 p token b) s t}

end StatMech.GrahamGHS.FourColor

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute.Part13
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalStableRawSquareOutputPredecessor_component_eq
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
    (hs : CanonicalStableRawSquareOutputPredecessor
      ends m j k l zero hloop hjk hkl hk0 p hno token s)
    (ht : CanonicalStableRawSquareOutputPredecessor
      ends m j k l zero hloop hjk hkl hk0 p hno token t) :
    canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno t := by
  rw [← canonicalStableRawTokenComponent_next
      ends m j k l zero hloop hjk hkl hk0 p hno s,
    ← canonicalStableRawTokenComponent_next
      ends m j k l zero hloop hjk hkl hk0 p hno t]
  apply canonicalStableRawTokenComponent_eq_of_target_eq
  exact hs.2.symm.trans ht.2


theorem canonicalStableRawSelfReroute_stateTokenIncidence
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
    CanonicalStableRawStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawSelfRerouteLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno s hself) s := by
  dsimp only [CanonicalStableRawStateTokenIncidence]
  refine ⟨Or.inl rfl, ?_, ?_⟩
  · exact (canonicalStableRawExceptionalEdgeNext_square
      ends m j k l zero hloop hjk hkl hk0 p hno s).1
  · exact (canonicalStableRawExceptionalEdgeNext_square
      ends m j k l zero hloop hjk hkl hk0 p hno s).2.1


theorem canonicalStableRawSelfOwnerReroute_stateTokenIncidence
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
    CanonicalStableRawStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawSelfOwnerRerouteLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno s hself) s := by
  dsimp only [CanonicalStableRawStateTokenIncidence]
  refine ⟨Or.inr rfl, ?_, ?_⟩
  · exact (canonicalStableRawExceptionalEdgeNext_square
      ends m j k l zero hloop hjk hkl hk0 p hno s).1
  · exact (canonicalStableRawExceptionalEdgeNext_square
      ends m j k l zero hloop hjk hkl hk0 p hno s).2.1


end StatMech.GrahamGHS.FourColor

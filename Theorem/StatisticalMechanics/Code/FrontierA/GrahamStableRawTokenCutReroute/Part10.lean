/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute.Part9
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalStableRawWitnessedStateTokenIncidence_iff
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (token : CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) :
    CanonicalStableRawWitnessedStateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p token s ↔
      CanonicalStableRawStateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p token s := by
  classical
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    rcases h.1 with hsource | howner
    · by_cases hexceptional : CanonicalStableRawLeftTokenIsExceptional
          ends m j k l zero hloop hjk hkl hk0 p token
      · exact ⟨CanonicalStableRawStateTokenIncidenceKind.sourceExceptional
          hsource hexceptional⟩
      · exact ⟨CanonicalStableRawStateTokenIncidenceKind.sourceFree
          hsource hexceptional⟩
    · by_cases hexceptional : CanonicalStableRawLeftTokenIsExceptional
          ends m j k l zero hloop hjk hkl hk0 p token
      · exact ⟨CanonicalStableRawStateTokenIncidenceKind.ownerExceptional
          howner hexceptional⟩
      · exact ⟨CanonicalStableRawStateTokenIncidenceKind.ownerFree
          howner hexceptional⟩


end StatMech.GrahamGHS.FourColor

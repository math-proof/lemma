/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute.Part4
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalStableRawDirectLeftToken_injective
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I) :
    Function.Injective fun s :
        {s : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p //
          s.target.1 ≠ canonicalStableRawSelfBase
            ends m j k l zero hloop hjk hkl hk0 p s.source} =>
      canonicalStableRawDirectLeftToken
        ends m j k l zero hloop hjk hkl hk0 p s.1 s.2 := by
  classical
  intro s t hst
  unfold canonicalStableRawDirectLeftToken at hst
  apply Subtype.ext
  apply canonicalStableRawExceptionalEdge_eq_of_source_target_eq
  · exact congrArg Sigma.fst hst
  · apply Subtype.ext
    exact congrArg (fun token => token.2.1) hst


end StatMech.GrahamGHS.FourColor

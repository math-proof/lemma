/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute.Part17
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


structure CanonicalStableRawReferenceAlternateData
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c r : ↑(canonicalRawCommonClosure ends m j k l zero p)) where
  target : leftSourceMaskFiber ends m j k l zero p
  sourceRelated : CanonicalRawGateRelated ends m j k l zero p c.1 target
  referenceRelated : CanonicalRawGateRelated ends m j k l zero p r.1 target
  target_ne_referenceSelf : target ≠ canonicalStableRawSelfBase
    ends m j k l zero hloop hjk hkl hk0 p r


end StatMech.GrahamGHS.FourColor

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferAmbientQuadrangle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferCoverageExchange.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferAmbientQuadrangle.Part3
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalQuadrangleCompletionSourceEquiv_commute
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (a b r s : leftMaskFiber ends m j k l zero p)
    (x : leftSourceMaskFiber ends m j k l zero p) :
    canonicalQuadrangleCompletionSourceEquiv
        ends m j k l zero hloop hjk hkl p a b
        (canonicalQuadrangleCompletionSourceEquiv
          ends m j k l zero hloop hjk hkl p r s x) =
      canonicalQuadrangleCompletionSourceEquiv
        ends m j k l zero hloop hjk hkl p r s
        (canonicalQuadrangleCompletionSourceEquiv
          ends m j k l zero hloop hjk hkl p a b x) := by
  apply Subtype.ext
  exact canonicalQuadrangleCompletion_changes_commute
    ends m k zero a.1.1 b.1.1 r.1.1 s.1.1 x.1


end StatMech.GrahamGHS.FourColor

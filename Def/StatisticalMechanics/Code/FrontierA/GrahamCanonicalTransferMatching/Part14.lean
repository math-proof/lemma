/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferComponentCut.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferMatching.Part13
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


def CanonicalCoverageExclusiveBoundaryCertificate
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (a b c : leftMaskFiber ends m j k l zero p) : Prop :=
  let d := canonicalQuadrangleCompletion ends m k zero
    a.1.1 b.1.1 c.1.1
  ((StatMech.Sharpness.RandomCurrent.connK
        ends (rowClass m d 0) k zero ∧
      StatMech.Sharpness.RandomCurrent.sources
        ends (edgeComponent ends (rowClass m d 0) zero) = {j, k} ∧
      StatMech.Sharpness.RandomCurrent.sources ends (rowClass m d 0 \
        edgeComponent ends (rowClass m d 0) zero) = ∅ ∧
      Disjoint (canonicalTransferUnion ends m k zero d)
        (rowClass m d 0 \
          edgeComponent ends (rowClass m d 0) zero)) ∨
    (StatMech.Sharpness.RandomCurrent.connK
        ends (rowClass m d 1) k zero ∧
      StatMech.Sharpness.RandomCurrent.sources
        ends (edgeComponent ends (rowClass m d 1) k) = {k, l} ∧
      StatMech.Sharpness.RandomCurrent.sources ends (rowClass m d 1 \
        edgeComponent ends (rowClass m d 1) k) = ∅ ∧
      Disjoint (canonicalTransferUnion ends m k zero d)
        (rowClass m d 1 \
          edgeComponent ends (rowClass m d 1) k)))


end StatMech.GrahamGHS.FourColor

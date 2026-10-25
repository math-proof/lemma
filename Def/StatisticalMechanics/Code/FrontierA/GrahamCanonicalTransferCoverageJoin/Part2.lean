/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCoverageJoin.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferCoverageDirected.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferCoverageJoin
open Finset


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def canonicalMaskOrbitCoverageJoin
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hclosed : CanonicalMaskOrbitCoverageUnionClosed
      ends m j k l zero p)
    (r s : leftMaskFiber ends m j k l zero p)
    (hrs : CanonicalMaskTransferOrbit ends m j k l zero p r s) :
    leftMaskFiber ends m j k l zero p :=
  Classical.choose
    ((canonicalMaskOrbitCoverageJoinCandidates
      ends m j k l zero p r s).exists_min_image
        (canonicalMaskOrbitScore ends m k zero p (j := j) (l := l))
        (canonicalMaskOrbitCoverageJoinCandidates_nonempty
          ends m j k l zero p hclosed r s hrs))

end StatMech.GrahamGHS.FourColor

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCoverageDirected.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferCommonGood.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferCoverageDirected.Part2
open Finset


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


def CanonicalMaskOrbitCoverageDirected
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Prop :=
  ∀ r s : leftMaskFiber ends m j k l zero p,
    CanonicalMaskTransferOrbit ends m j k l zero p r s ->
      ∃ t : leftMaskFiber ends m j k l zero p,
        CanonicalMaskTransferOrbit ends m j k l zero p r t ∧
          ∀ d : leftMaskFiber ends m j k l zero p,
            CanonicalMaskTransferOrbit ends m j k l zero p r d ->
            (CanonicalTransferWorks ends m k zero r.1.1 d.1.1 ∨
              CanonicalTransferWorks ends m k zero s.1.1 d.1.1) ->
            CanonicalTransferWorks ends m k zero t.1.1 d.1.1


noncomputable def canonicalMaskOrbitMaxCoverageReference
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftMaskFiber ends m j k l zero p) :
    leftMaskFiber ends m j k l zero p :=
  Classical.choose
    ((canonicalMaskTransferOrbitFinset ends m j k l zero p c).exists_max_image
      (fun r => #(canonicalMaskOrbitCoverage ends m j k l zero p r))
      (canonicalMaskTransferOrbitFinset_nonempty
        ends m j k l zero p c))

end StatMech.GrahamGHS.FourColor

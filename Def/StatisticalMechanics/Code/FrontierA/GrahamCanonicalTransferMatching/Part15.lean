/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferComponentCut.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferMatching.Part14
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


def CanonicalMaskRightTightRootCutExcluded
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Prop :=
  ∀ S : Finset (leftMaskFiber ends m j k l zero p),
    S.Nonempty ->
    (canonicalMaskRightNeighborhood
      ends m j k l zero p S).card + 1 = S.card ->
    ∀ r ∈ S, ∀ c ∈ S,
      ¬ CanonicalTranslatedRowRootComponentCut
        ends m k zero r.1.1 c.1.1


noncomputable def canonicalMaskRightRestrictedCoverage
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (r : leftMaskFiber ends m j k l zero p) :
    Finset (leftMaskFiber ends m j k l zero p) := by
  classical
  exact S.filter fun c =>
    CanonicalTransferWorks ends m k zero r.1.1 c.1.1

end StatMech.GrahamGHS.FourColor

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferAmbientQuadrangle.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalCollisionSquare
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalEdgeDegreeHall.Part6
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferMatching.Part16
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamGateDiscrepancy.Part15
import Def.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part14
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalRawCommonClosureIter_subset_succ
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) (n : Nat) :
    canonicalRawCommonClosureIter ends m j k l zero p n ⊆
      canonicalRawCommonClosureIter ends m j k l zero p (n + 1) :=
  StatMech.FrontierA.finiteCommonClosureIter_subset_succ _ _ _ _ n

theorem exists_canonicalRawCommonClosureIter_fixed
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    ∃ n ≤ Fintype.card (leftSourceMaskFiber ends m j k l zero p) -
        (canonicalRawNegativeGateFinset ends m j k l zero p).card,
      canonicalRawCommonClosureIter ends m j k l zero p (n + 1) =
        canonicalRawCommonClosureIter ends m j k l zero p n :=
  StatMech.FrontierA.exists_finiteCommonClosureIter_fixed _ _ _ _

end StatMech.GrahamGHS.FourColor

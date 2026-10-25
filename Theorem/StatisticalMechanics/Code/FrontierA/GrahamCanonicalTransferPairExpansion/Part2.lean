/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferPairExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferGF2.Part3
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferPairExpansion.Part2
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalMaskOrbitCoveragePairProgress_of_pairExpansion
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hexpand : CanonicalMaskOrbitCoveragePairExpansion
      ends m j k l zero p) :
    CanonicalMaskOrbitCoveragePairProgress ends m j k l zero p := by
  intro a b hab ha hb
  exact Or.inr (hexpand a b hab ha hb)


end StatMech.GrahamGHS.FourColor

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWRectangleCritical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.KWSpectralCritical
import Def.StatisticalMechanics.Code.Onsager.KWRectangleCritical.Part2


namespace StatMech.Onsager

open Matrix BigOperators

open scoped Matrix.Norms.L2Operator


@[simp]
theorem ons_rectTailDartEquiv_apply (M N : Nat) (d : ons_RectDart M N) :
    ons_rectTailDartEquiv M N d =
      (ons_rectDirStep M N (d.2 + 2) d.1, d.2) := rfl


end StatMech.Onsager

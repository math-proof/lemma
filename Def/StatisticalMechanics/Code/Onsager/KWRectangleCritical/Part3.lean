/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWRectangleCritical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.KWSpectralCritical
import Theorem.StatisticalMechanics.Code.Onsager.KWRectangleCritical


namespace StatMech.Onsager

open Matrix BigOperators

open scoped Matrix.Norms.L2Operator


def ons_rectDartBoundaryRank (M N : Nat) (d : ons_RectDart M N) : Nat :=
  match d.2 with
  | 0 => d.1.1.val + 1
  | 1 => d.1.2.val + 1
  | 2 => M - d.1.1.val + 1
  | 3 => N - d.1.2.val + 1

end StatMech.Onsager
